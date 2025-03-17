# Copyright (c) Microsoft Corporation. All rights reserved.
# Licensed under the MIT license.

import simpy
import random
import numpy as np
import logging
import multiprocessing
import threading
from functools import partial
from enum import Enum
from copy import deepcopy


class AdaptiveStatsMonitor:
    """Monitors and computes statistics for adaptive delay calculations."""

    def __init__(self, smoothing_factor=2 / (10 + 1), ddof=1):
        # Exponential moving average parameters
        self.smoothing_factor = smoothing_factor
        self.ema = 400  # Initial estimate

        # Standard deviation calculation parameters (Welford's algorithm)
        self.ddof = ddof
        self.count = 0
        self.mean = 0.0
        self.M2 = 0.0

    def include(self, operation_time):
        """Include a new operation time in the statistics."""
        # Update the exponential moving average
        self.ema = (
            self.smoothing_factor * operation_time
            + (1 - self.smoothing_factor) * self.ema
        )

        # Update standard deviation using Welford's online algorithm
        self.count += 1
        delta = operation_time - self.mean
        self.mean += delta / self.count
        delta2 = operation_time - self.mean
        self.M2 += delta * delta2

    def get(self):
        """Get the current EMA and standard deviation."""
        if self.count > 0:
            variance = self.M2 / self.count
        else:
            variance = 100  # Default variance when no samples
        return self.ema, np.sqrt(variance)


class Acceptor:
    """
    Represents an Acceptor in the Paxos protocol, responsible for accepting or
    rejecting proposals from Proposers based on the ballot number.
    """

    def __init__(self, id):
        self.id = id
        self.promised_ballot_number = -1
        self.accepted_ballot_number = -1
        self.adaptive_stats_monitor = AdaptiveStatsMonitor()

    def prepare(self, ballot_num):
        """
        Receives a prepare request from a Proposer and determines whether to promise to accept the proposal.

        Returns:
            bool: True if the promise is made, False otherwise.
        """
        if ballot_num > self.promised_ballot_number:
            self.promised_ballot_number = ballot_num
            return True
        else:
            return False

    def accept(self, ballot_num, adaptive_stats_monitor):
        """
        Receives an accept request from a Proposer and determines whether to accept the value.

        Returns:
            bool: True if the value is accepted, False otherwise.
        """
        if ballot_num >= self.promised_ballot_number:
            self.promised_ballot_number = ballot_num
            self.accepted_ballot_number = ballot_num
            self.adaptive_stats_monitor = adaptive_stats_monitor
            return True
        else:
            return False


class DocumentStore:
    """
    Represents a document store that has acceptor state, handles read and write operations.
    """

    def __init__(self, env, acceptor):
        self.etag = 0
        self.env = env
        self.acceptor = acceptor

    def put(self, etag, new_acceptor, client_delay, server_delay):
        """
        Performs a write operation on the document store.

        Returns:
            bool: True if the write operation is successful, False otherwise.
        """
        yield self.env.timeout(client_delay)
        if etag == self.etag:
            self.etag += 1
            self.acceptor = new_acceptor
            success = True
        else:
            success = False
        yield self.env.timeout(server_delay)
        return success

    def get(self, client_delay, server_delay):
        """
        Performs a read operation on the document store.

        Returns:
            tuple: A tuple containing the etag and the Acceptor state.
        """
        yield self.env.timeout(client_delay)
        etag = self.etag
        acceptor = deepcopy(self.acceptor)
        yield self.env.timeout(server_delay)
        return etag, acceptor


class QuorumChecker:
    """Tracks acknowledgments and checks if a quorum has been reached."""

    def __init__(self, quorum):
        self.quorum = quorum
        self.count = 0

    def ack(self):
        """
        Increment acknowledgment count and check if quorum is reached.

        Returns:
            bool: True if quorum is reached, False otherwise.
        """
        self.count += 1
        return self.count >= self.quorum


class OperationTime:
    """
    Manages generation of realistic network latencies between clients and servers.
    """

    def __init__(self):
        self.mean_latency = random.uniform(50, 400)  # 50 ms to 400 ms
        self.std_dev = self.mean_latency * 0.1

    def get_client_server_latency(self):
        """
        Generate random client and server delays based on a normal distribution.

        Returns:
            tuple: (client_delay, server_delay) in milliseconds
        """
        client_delay = np.random.normal(self.mean_latency / 2, self.std_dev / 2)
        server_delay = np.random.normal(self.mean_latency / 2, self.std_dev / 2)
        return client_delay, server_delay


class Proposer:
    """
    Represents a Proposer in the Paxos protocol, responsible for proposing values
    to Acceptors and reaching consensus.
    """

    class PhaseResponse(Enum):
        NAK = 1
        DONE = 2

    def __init__(
        self,
        env,
        id,
        document_stores,
        simulation_stats_collector,
        lease_enforcer_timeout,
        proposer_run_interval,
    ):
        # Proposer variables
        self.id = id
        self.retry_count = 0
        self.ballot_num = -1
        self.document_stores = document_stores
        self.quorum = len(self.document_stores) // 2 + 1
        self.accept_phase_start_time = None
        self.accept_phase_take_time = None

        # Simulation variables
        self.env = env
        self.lease_enforcer_timeout = lease_enforcer_timeout
        self.proposer_run_interval = proposer_run_interval
        self.simulation_stats_collector = simulation_stats_collector

        # This provides a more realistic simulation for proposer and store communication.
        # For example, a user region(proposer) in the CosmosDB that communicates with a fault-tolerant document store region
        # most likely exhibits consistent performance. For each proposer, we randomly assign latency distribution to each acceptor document store.
        self.randomized_store_latency_mapping = {
            store: OperationTime() for store in document_stores
        }
        self.latest_start_time_of_prepare = None
        self.adaptive_stats_monitor = AdaptiveStatsMonitor()

    def reset(self):
        """Reset the retry count."""
        self.retry_count = 0

    def run_lease_enforcer(self):
        """
        Simulates a lease timeout that can interrupt ongoing operations.
        """
        try:
            yield self.env.timeout(self.lease_enforcer_timeout)
        except simpy.Interrupt:
            pass

    def run(self):
        """
        Main execution loop that runs the Paxos protocol at regular intervals.
        """
        previous_run_succeed = False
        while True:
            assert self.lease_enforcer_timeout > self.proposer_run_interval

            lease_enforcer_process = self.env.process(self.run_lease_enforcer())

            # Wait appropriate time between runs
            if self.latest_start_time_of_prepare:
                time_took_to_complete = self.env.now - self.latest_start_time_of_prepare
                yield self.env.timeout(
                    self.proposer_run_interval - time_took_to_complete
                )
            else:
                yield self.env.timeout(self.proposer_run_interval)

            self.reset()

            logging.debug(
                f"Proposer {self.id} is starting to propose at {self.env.now}."
            )
            paxos_process = self.env.process(self.prepare_phase())

            # Wait for first completing process
            if not previous_run_succeed:
                yield paxos_process
            else:
                yield self.env.any_of([lease_enforcer_process, paxos_process])

            if lease_enforcer_process.triggered and previous_run_succeed:
                # Lease enforcer triggered means the proposer didn't complete in time
                # Record failure here, interrupt paxos_process
                # This represents replica fault
                self.simulation_stats_collector.record_failure()
                logging.debug(
                    f"There was a failure for Proposer {self.id} at {self.env.now}"
                )
                self.latest_start_time_of_prepare = None
                previous_run_succeed = False
                paxos_process.interrupt()
            elif paxos_process.triggered:
                # Paxos process triggered means proposer completed
                # Record success here, interrupt lease_enforcer_process
                previous_run_succeed = True
                self.simulation_stats_collector.record_success()
                if not lease_enforcer_process.triggered:
                    lease_enforcer_process.interrupt()
            else:
                assert False, "Either lease enforcer or paxos completes"

    def prepare_phase(self):
        """
        Initiates the Prepare Phase of the Paxos protocol, generating a new ballot number
        and sending prepare requests to Acceptors.
        """
        self.latest_start_time_of_prepare = self.env.now
        self.ballot_num = int(self.env.now)
        logging.debug(
            f"Proposer {self.id} picked ballot number {self.ballot_num} at {self.env.now:.2f}ms."
        )
        try:
            yield self.env.process(self.promise_phase())
        except simpy.Interrupt:
            pass

    def promise_phase(self):
        """
        Handles the Promise Phase of the Paxos protocol, waiting for promises from a quorum of Acceptors.
        """
        logging.debug(
            f"Proposer {self.id} sending prepare messages with ballot number: {self.ballot_num}"
        )

        max_voted_value = [None]  # Using list as mutable container
        send_prepare_function = partial(
            self.send_prepare,
            max_voted_value=max_voted_value,
        )
        can_move_to_next_phase = yield self.env.process(
            self.send_and_wait_for_quorum(send_prepare_function, "promise")
        )
        if can_move_to_next_phase:
            yield self.env.process(self.accept_phase(max_voted_value[0]))
        else:
            yield self.env.process(self.handle_nak_message())

    def accept_phase(self, max_voted_value):
        """
        Handles the Accept Phase of the Paxos protocol, transitioning to the accepted state after a simulated delay.
        """
        # Edit value
        self.adaptive_stats_monitor = max_voted_value.adaptive_stats_monitor
        if self.accept_phase_take_time:
            self.adaptive_stats_monitor.include(self.accept_phase_take_time)

        # Record new phase start time as we track phase2 completion times
        self.accept_phase_start_time = self.env.now
        self.accept_phase_take_time = None

        yield self.env.process(self.accepted_phase(max_voted_value))

    def accepted_phase(self, new_value):
        """
        Handles the Accepted Phase of the Paxos protocol, waiting for acceptance from a quorum of Acceptors.
        """
        logging.debug(
            f"Proposer {self.id} sending accept messages at {self.env.now:.2f}ms with ballot number: {self.ballot_num}"
        )
        send_accept_lambda = lambda store, accepted_response_queue: self.send_accept(
            store, accepted_response_queue, new_value
        )
        value_accepted_by_majority = yield self.env.process(
            self.send_and_wait_for_quorum(send_accept_lambda, "accepted")
        )
        if value_accepted_by_majority:
            logging.debug(
                f"Proposer {self.id} completed paxos round at {self.env.now:.2f}ms with ballot number {self.ballot_num}"
            )
            # Record phase completion time here. This information is going to be proposed in the next run
            self.accept_phase_take_time = self.env.now - self.accept_phase_start_time
        else:
            yield self.env.process(self.handle_nak_message())

    def send_and_wait_for_quorum(self, send_function, phase_id):
        """
        Resolves the quorum for a given phase of the Paxos protocol.

        Args:
            send_function (function): The function to send messages to acceptors.
            phase_id (string): The string identifier of the paxos phase

        Returns:
            bool: True if send messages is successful (quorum achieved), False otherwise.
        """
        quorum_checker = QuorumChecker(self.quorum)
        response_queue = simpy.Store(self.env, capacity=len(self.document_stores))

        # Start processes to send messages to all document stores
        for document_store in self.document_stores:
            self.env.process(send_function(document_store, response_queue))

        # Wait for responses
        while True:
            (acceptor_id, phase_response) = yield response_queue.get()
            if phase_response == Proposer.PhaseResponse.NAK:
                logging.debug(
                    f"Proposer {self.id} got a NAK response for ballot number {self.ballot_num} from Acceptor {acceptor_id} at {self.env.now:.2f}ms in {phase_id} phase"
                )
                # break on first NAK
                return False

            logging.debug(
                f"Proposer {self.id} got a success response for ballot number {self.ballot_num} from Acceptor {acceptor_id} at {self.env.now:.2f}ms in {phase_id} phase"
            )
            quorum_completed = quorum_checker.ack()
            if quorum_completed:
                logging.debug(
                    f"Proposer {self.id} achieved quorum of success messages at {self.env.now:.2f} in {phase_id} phase with ballot number {self.ballot_num}"
                )
                return True

    def send_prepare(self, store, prepare_response_queue, max_voted_value):
        """
        Sends a prepare request to an Acceptor and handles the response.

        Args:
            store (DocumentStore): The document store to send the prepare request to.
            prepare_response_queue (simpy.Store): The response queue to store the prepare response.
            max_voted_value (list): Mutable container to store the max voted value found.
        """
        # Read
        (etag, acceptor) = yield self.env.process(self.read_document(store))

        # Modify
        is_nak_message = not acceptor.prepare(ballot_num=self.ballot_num)

        if is_nak_message:
            prepare_response_queue.put((acceptor.id, Proposer.PhaseResponse.NAK))
            return

        # Find the max voted value, this is similar to StartPhase2 in LeaderStateMachine
        if (
            not max_voted_value[0]
            or acceptor.accepted_ballot_number
            >= max_voted_value[0].accepted_ballot_number
        ):
            max_voted_value[0] = acceptor

        # Write
        write_succeed = yield self.env.process(
            self.write_document(etag, store, acceptor)
        )
        if write_succeed:
            prepare_response_queue.put((acceptor.id, Proposer.PhaseResponse.DONE))
        else:
            logging.debug(
                f"Proposer {self.id} got etag mismatch with prepare messages, acceptor {acceptor.id} etag {etag}, but store etag {store.etag} at {self.env.now:.2f}"
            )
            yield self.env.process(
                self.send_prepare(
                    store,
                    prepare_response_queue,
                    max_voted_value=max_voted_value,
                )
            )

    def send_accept(self, store, accepted_response_queue, new_value):
        """
        Sends an accept request to an Acceptor and handles the response.

        Args:
            store (DocumentStore): The document store to send the accept request to.
            accepted_response_queue (simpy.Store): The response queue to store the accept response.
            new_value (Acceptor): The new value to be accepted.
        """
        # Read
        (etag, acceptor) = yield self.env.process(self.read_document(store))

        # Modify
        accepted = acceptor.accept(
            ballot_num=self.ballot_num,
            adaptive_stats_monitor=new_value.adaptive_stats_monitor,
        )

        if not accepted:
            accepted_response_queue.put((acceptor.id, Proposer.PhaseResponse.NAK))
            return

        # Write
        write_succeed = yield self.env.process(
            self.write_document(etag, store, acceptor)
        )
        if write_succeed:
            accepted_response_queue.put((acceptor.id, Proposer.PhaseResponse.DONE))
        else:
            logging.debug(
                f"Proposer {self.id} got etag mismatch with accept messages, acceptor {acceptor.id} etag {etag}, but store etag {store.etag} at {self.env.now:.2f}"
            )
            yield self.env.process(
                self.send_accept(store, accepted_response_queue, new_value)
            )

    def handle_nak_message(self):
        """
        Handles a NAK message by incrementing the retry count, calculating the retry delay,
        and initiating a new prepare phase.
        """
        self.retry_count += 1
        (ema, std_dev) = self.adaptive_stats_monitor.get()
        nak_delay = (ema + std_dev) * random.randint(0, 2 ** (self.retry_count - 1))
        yield self.env.timeout(nak_delay)
        yield self.env.process(self.prepare_phase())

    def read_document(self, store):
        """
        Performs a read operation on a document store.

        Returns:
            tuple: A tuple containing the etag and the Acceptor state.
        """
        logging.debug(
            f"Proposer {self.id} is reading a document from Acceptor {store.acceptor.id} at {self.env.now}."
        )
        client_delay, server_delay = self.get_randomized_store_delay(store)
        result = yield self.env.process(store.get(client_delay, server_delay))
        logging.debug(
            f"Proposer {self.id} read a document from Acceptor {store.acceptor.id} at {self.env.now}."
        )
        return result

    def write_document(self, etag, store, new_acceptor):
        """
        Performs a write operation on a document store.

        Returns:
            bool: True if the write operation is successful, False otherwise.
        """
        logging.debug(
            f"Proposer {self.id} is writing a document to Acceptor {store.acceptor.id} at {self.env.now}."
        )
        client_delay, server_delay = self.get_randomized_store_delay(store)
        result = yield self.env.process(
            store.put(etag, new_acceptor, client_delay, server_delay)
        )
        logging.debug(
            f"Proposer {self.id} wrote a document to Acceptor {store.acceptor.id} at {self.env.now}."
        )
        return result

    def get_randomized_store_delay(self, store):
        """
        Retrieves the randomized store delay for a given document store.

        Returns:
            tuple: A tuple containing the client-side delay and the server-side delay.
        """
        store_operation_time = self.randomized_store_latency_mapping[store]
        return store_operation_time.get_client_server_latency()


class SimulationStatisticCollector:
    """Collects and tracks simulation statistics."""

    def __init__(self):
        self.success = 0
        self.failure = 0

    def record_success(self):
        """Record a successful operation."""
        self.success += 1

    def record_failure(self):
        """Record a failed operation."""
        self.failure += 1


def simulate_proposers(env, proposers, iteration_run_time):
    """
    Simulates the Paxos protocol with multiple Proposers and Acceptors.

    Args:
        env (simpy.Environment): The simulation environment.
        proposers (list): List of Proposer instances.
        iteration_run_time (int): The duration of the simulation in milliseconds.
    """
    for proposer in proposers:
        env.process(proposer.run())
    yield env.timeout(iteration_run_time)


def run_single_iteration(params):
    """
    Run a single simulation iteration.

    Args:
        params (tuple): A tuple containing all parameters needed for the simulation.

    Returns:
        tuple: (iteration_num, failures, successes) from this iteration
    """
    (
        iteration_num,
        num_proposers,
        num_acceptors,
        iteration_run_time,
        lease_enforcer_timeout,
        proposer_run_interval,
        total_iterations,
    ) = params

    env = simpy.Environment()
    simulation_stats_collector = SimulationStatisticCollector()

    # Create acceptors and document stores
    acceptors = [Acceptor(i) for i in range(num_acceptors)]
    document_stores = [DocumentStore(env, acceptor) for acceptor in acceptors]

    # Create proposers
    proposers = [
        Proposer(
            env,
            i,
            document_stores,
            simulation_stats_collector,
            lease_enforcer_timeout,
            proposer_run_interval,
        )
        for i in range(num_proposers)
    ]

    # Run the simulation
    proc = env.process(simulate_proposers(env, proposers, iteration_run_time))
    env.run(until=proc)

    return (
        iteration_num,
        simulation_stats_collector.failure,
        simulation_stats_collector.success,
    )


# Global lock for synchronizing progress updates
progress_lock = threading.Lock()


def progress_callback(result):
    """
    Callback function to track progress of simulation iterations.
    TODO: This is highly contested and can be improved, but for now, it is good enough.

    Args:
        result (tuple): (iteration_num, failures, successes) from a completed iteration
    """
    iteration_num, _, _ = result
    # Use a global variable to track progress
    global completed_iterations, total_iterations
    with progress_lock:
        completed_iterations += 1
        if (
            completed_iterations % min(total_iterations, 10) == 0
            or completed_iterations == total_iterations
        ):
            logging.info(
                f"Progress: {completed_iterations}/{total_iterations} iterations completed ({(completed_iterations/total_iterations*100):.1f}%)"
            )


def perform_simulation(
    num_proposers,
    num_acceptors,
    iteration_run_time,
    lease_enforcer_timeout,
    proposer_run_interval,
    num_iterations,
):
    """
    Performs multiple simulation iterations in parallel and collects statistics.

    Args:
        num_proposers (int): Number of proposers in the simulation.
        num_acceptors (int): Number of acceptors in the simulation.
        iteration_run_time (int): Duration of each simulation in milliseconds.
        lease_enforcer_timeout (int): Timeout for the lease enforcer in milliseconds.
        proposer_run_interval (int): Interval between proposer runs in milliseconds.
        num_iterations (int): Number of simulation iterations to run.
    """
    # Initialize global tracking variables
    global completed_iterations, total_iterations
    completed_iterations = 0
    total_iterations = num_iterations

    # Prepare parameters for each iteration
    params = [
        (
            i,
            num_proposers,
            num_acceptors,
            iteration_run_time,
            lease_enforcer_timeout,
            proposer_run_interval,
            num_iterations,
        )
        for i in range(num_iterations)
    ]

    # Determine optimal number of processes based on CPU cores
    num_processes = min(multiprocessing.cpu_count(), num_iterations)

    # Run simulations in parallel
    logging.info(
        f"Starting {num_iterations} iterations using {num_processes} parallel processes"
    )

    # Create a multi-processing manager for shared progress tracking
    results = []
    with multiprocessing.Pool(processes=num_processes) as pool:
        # Use imap to process results as they come in
        for result in pool.imap_unordered(run_single_iteration, params):
            results.append(result)
            progress_callback(result)

    # Aggregate results
    total_failures = sum(failure for _, failure, _ in results)
    total_success = sum(success for _, _, success in results)

    # Calculate and report final statistics
    total_operations = total_failures + total_success
    if total_operations > 0:
        failure_rate = (total_failures / total_operations) * 100
    else:
        failure_rate = 0

    logging.info(
        f"Completed {num_iterations} simulations with {iteration_run_time} ms run per simulation\n"
        f"Proposer count: {num_proposers}, Acceptor count: {num_acceptors}\n"
        f"Total succeed proposer rounds: {total_success}\n"
        f"Total failed proposer rounds: {total_failures}\n"
        f"Failure rate:  {failure_rate:.3f}%\n"
        f"Lease enforcer timeout: {lease_enforcer_timeout} ms and Proposer run interval {proposer_run_interval} ms."
    )


# Global variables for tracking progress
completed_iterations = 0
total_iterations = 0

if __name__ == "__main__":
    # Configure logging with simpler format focused on the message
    logging.basicConfig(
        format="%(asctime)s - %(levelname)s - %(message)s", level=logging.INFO
    )

    # 7 proposers, 7 acceptors, 1 hour run time, 45 sec lease enforcer, 30 sec proposer interval, 10000 iterations
    test_cases = [(7, 7, 1 * 60 * 60 * 1000, 45000, 30000, 10000)]
    for (
        num_proposers,
        num_acceptors,
        iteration_run_time,
        lease_enforcer_timeout,
        proposer_run_interval,
        num_iterations,
    ) in test_cases:
        perform_simulation(
            num_proposers,
            num_acceptors,
            iteration_run_time,
            lease_enforcer_timeout,
            proposer_run_interval,
            num_iterations,
        )
