\* Copyright (c) Microsoft Corporation. All rights reserved.
\* Licensed under the MIT license.

------------------------- MODULE WriteRegionFailoverPolicy -------------------------
EXTENDS FiniteSets, Integers, TLC, Sequences

CONSTANT
    \* A set of regions in the system. Example: A set of 3 regions, {"r1", "r2", "r3"}
    Regions

(*
    This model is a demonstration of a write region selection policy that performs graceful 
    failovers to the user's preferred write region, and non-graceful failovers to highest 
    progressed region, asserting that there is no data loss for correctness and a write region
    will be chosen eventually when regions are stable for liveness
*)

VARIABLE
    \*
    \* HELPER VARIABLES (MODEL ONLY)
    \* -----------------------------
    \* These variables are not consulted for actions, but used for validating correctness.
    \*
    \* This keeps track of the last read value by the client, and used in validating
    \* 'ReadProperty' assertion
    LastReadData,
    \* This keeps track of alive regions set, and whether a write region was alive, for
    \* each Time Tick in the system, and is used in validating the
    \* 'AssertWriteRegionIsChosenWhenMajoritySetIsHeartbeating' assertion
    RegionStateHistory,
    \* Monotonically increasing data generator which is used to perform client writes across
    \* regions. This helps in performing 'ReadProperty' validation
    NextDataToWrite,
    IsPreferredWriteRegionChangedInCurrentTick,

    \* REGION LOCAL VARIABLES
    \* ----------------------
    \* These variables represent current state of a region tracked on the regions themselves
    \* i.e. these variables are NOT stored in the global state but obtained by reading the 
    \* respective region replicas themselves
    \*
    \* The latest LSN value that has been committed locally on a region, tracked per-region
    RegionLatestCommittedUptoLSN,
    \* Committed data values at each possible LSN value on a region, tracked per-region
    RegionCommittedDataAtLSN,
    \* Globally committed upto LSN value (GCLSN) from the perspective of each region, tracked per-region
    RegionGCLSN,
    \* Per-region variable, which represents which client request types are accepted by a region
    RegionCurrentServiceStatus,
    \* Per-region variable, which represents the Computed Topology for the corresponding region to apply
    RegionLatestComputedTopology,
    \* Per-region variable, which represents the tick's Computed Topology that was successfully applied on the region
    RegionLastAppliedComputedTopologyTick,
    \* Per-region variable, which represents the most recent topology configuration that was successfully applied on the region
    RegionCurrentTopologyConfigNumber,
    \* Per-region variable, which represents the topology upsert intent which comes from external source e.g Control Plane"
    RegionCurrentTopologyUpsertIntent,
    \* Per-region variable, which represents the build status of the region
    RegionCurrentBuildStatus,
    \* This represents progress of a global wall clock in unit of ticks
    CurrentClockTick,

    \* GLOBAL STATE VARIABLES
    \* ----------------------
    \* All the below variables with a prefix of 'Global' must be stored in the global state
    \* i.e. global consensus store
    \*
    GlobalCurrentWriteRegion,
    GlobalPreferredWriteRegion,
    \* Represents if there is an on-going failover, and what kind of failover
    GlobalFailoverStatus,
    \* The clock tick at which GlobalFailoverStatus was last updated
    GlobalFailoverStatusLastChangedClockTick,
    \* 
    \* Global config number represents a change in the following global state variables
    \* 1. GlobalCurrentWriteRegion
    \* 2. GlobalFailoverStatus
    \* i.e. in other words, if there is a change in the topology of regions
    \* GlobalConfigNumber is mapped to TargetFailoverManagerConfigurationNumber in our current implementation as of 08/05/2024
    GlobalConfigNumber,
    \* Target state for each of the corresponding regions to reach 
    \* to declare that the 'GlobalConfigNumber' is applied on that region
    \* For each topology computation, the 'GlobalRegionTargetServiceStatus' will
    \* reflect what is the desired state a region must reach for this topology
    GlobalRegionTargetServiceStatus,
    \* This following variable tracks per-region current configuration number the region is
    \* in. The possible values of this is obtained from the 'GlobalConfigNumber'
    \* Once the reported 'GlobalReportedRegionCurrentServiceStatus' becomes 'GlobalRegionTargetServiceStatus'
    \* for a region, this becomes equal to 'GlobalConfigNumber' for the respective region
    GlobalRegionCurrentGlobalConfigNumber,

    \* The following per-region variables track the regional reports from respective
    \* regions in the topology on the global state. These are also stored in the
    \* consensus store and are used to make decisions in failover process.
    GlobalReportedRegionTick,
    GlobalReportedRegionLatestCommittedUptoLSN,
    GlobalReportedRegionCurrentServiceStatus

MajorityRegionsSetSize == (Cardinality(Regions) \div 2) + 1

\* Tick threshold to declare a region as dead
NumberOfTicksToDeclareRegionAsDead == 1

\* Max number of ticks that are allowed for a graceful failover process
\* to execute. If the graceful failover goes beyond this point, it will be
\* aborted
GracefulFailoverExpirationTicks == NumberOfTicksToDeclareRegionAsDead + 1

\* Number of ticks of history to analyze to determine if a write
\* region is chosen when majority of regions are heartbeating to
\* global state
NumberOfHistoryTicksToLookback == GracefulFailoverExpirationTicks + 1

\* NOTE:
\* The tick space should be atleast 3 ticks to excercise
\* some invariants that are defined in this spec.
\* Ex: {0..5} with starting tick value of '2', where there
\* are 3 ticks starting from 2 until 5
\*
TickType == Nat

\* One value is enough for LSN type to test the correctness
\* of the spec
\* Ex: {1..2} starting with data already written for LSN '1'
\*
LSNType == Nat

\* NOTE:
\* Config number type should atleast have 2 values because
\* each failover step requires an increment in config, and
\* both GRACEFUL and UNGRACEFUL requires 2 steps to complete.
\* Ex: {1..3} with initial configuration number as '1'
\*
ConfigNumberType == Nat

NoFailoverInProgress == "NoFailoverInProgress"
GracefulFailoverInProgress == "GracefulFailoverInProgress"
UngracefulFailoverInProgress == "UngracefulFailoverInProgress"
WriteStatusRevokedByExternalSource == "WriteStatusRevokedByExternalSource"

GlobalFailoverStatusType == 
    {
        \* Performed when current write region is not the user's preferred
        \* region
        GracefulFailoverInProgress,
        \* Performed when current write region stops heartbeating with the
        \* global state
        UngracefulFailoverInProgress,
        NoFailoverInProgress,
        \* Performed when there is signal from external sources ( e.g Control plane sending intent in topology) to revoke the write status
        WriteStatusRevokedByExternalSource
    }
TopologyIntentTypeNone == "TopologyIntentTypeNone"
TopologyIntentTypeRevokeGlobalWriteStatus == "TopologyIntentTypeRevokeGlobalWriteStatus"
TopologyIntentTypeGrantGlobalWriteStatus == "TopologyIntentTypeGrantGlobalWriteStatus"
TopologyIntentTypeIncrementGlobalConfigurationNumber == "TopologyIntentTypeIncrementGlobalConfigurationNumber"
TopologyIntentType ==
    {
        TopologyIntentTypeNone,
        TopologyIntentTypeRevokeGlobalWriteStatus,
        TopologyIntentTypeGrantGlobalWriteStatus,
        TopologyIntentTypeIncrementGlobalConfigurationNumber
    }

ReadOnlyReplicationAllowed == "ReadOnlyReplicationAllowed"
ReadOnlyReplicationDisallowed == "ReadOnlyReplicationDisallowed"
ReadWrite == "ReadWrite"
ReadWriteWithWritesQuiesced == "ReadWriteWithWritesQuiesced"
NotHeartbeating == "NotHeartbeating"
ReadyForBuild == "ReadyForBuild"
BuildCompleted == "BuildCompleted"

RegionBuildStatusType ==
    {
        \* Region is ready to bootstrap its data.
        ReadyForBuild,
        \* Region has built data.
        \* Read region has built data from write region.
        \* Write region builts data from itself (no-op)
        BuildCompleted
    }

InitialBuildStatus == ReadyForBuild

RegionServiceStatusType ==
    {
        \* No operations can be performed, the region has lost
        \* its lease with global state. No client traffic
        \* or replication traffic is allowed on the region
        NotHeartbeating,
        \* Clients can perform ONLY reads on the region. 
        \* Replication traffic from write region is allowed.
        ReadOnlyReplicationAllowed,
        \* Clients can perform ONLY reads on the region.
        \* Replication traffic is NOT allowed from any other region.
        ReadOnlyReplicationDisallowed,
        \* Clients can perform both reads and writes on the region.
        \* Replication traffic to read regions is allowed.
        ReadWrite,
        \* Clients can perform ONLY reads on the region.
        \* Replication traffic to read regions is allowed. 
        \* When a graceful failover is being performed, the current 
        \* write region turns its status to this and continues replicating
        \* any pending writes to new write region
        ReadWriteWithWritesQuiesced
    }

InitialServiceStatus == NotHeartbeating

NextDataToWriteType == Nat

RegionLSNDataType == [
    Regions -> [LSNType -> NextDataToWriteType]
]

LastReadDataType == [
    Region : Regions,
    Data : NextDataToWriteType
]

InitialLSN == 1
InitialWrittenDataValue == 1

InvalidDataValue == 0
InvalidConfigNumber == -1
InvalidTick == -1

ComputedTopologyType == [
    TargetServiceStatus: RegionServiceStatusType,
    ConfigNumber: ConfigNumberType \union {InvalidConfigNumber}
]

NilComputedTopology == [
    TargetServiceStatus |-> NotHeartbeating,
    ConfigNumber |-> InvalidConfigNumber
]

\* Leaving two tick values '0' and '1'
\* in the tick space of {0..5} for
\* (previous - 1), and (previous) tick
StartingClockTick == 2

Init ==
    /\  GlobalCurrentWriteRegion \in Regions
    /\  RegionLatestCommittedUptoLSN = [region \in Regions |-> InitialLSN]
    /\  RegionGCLSN = [region \in Regions |-> InitialLSN]
    /\  NextDataToWrite = InitialWrittenDataValue + 1
    /\  LastReadData = [Region |-> GlobalCurrentWriteRegion, Data |-> InitialWrittenDataValue]
    /\  RegionCurrentServiceStatus = [region \in Regions |-> InitialServiceStatus]
    /\  RegionCurrentBuildStatus = [region \in Regions |-> InitialBuildStatus]
    /\  GlobalPreferredWriteRegion \in Regions
    /\  GlobalFailoverStatus = NoFailoverInProgress
    /\  GlobalConfigNumber = 1
    /\  CurrentClockTick = StartingClockTick
    \* In the following initial states, CurrentClockTick - 1 is necessary
    \* to ensure that regions are not incorrectly declared as
    \* heartbeating in the first tick i.e. '1'. This forces them to 
    \* perform heartbeat in the first tick to be declared as alive.
    /\  GlobalFailoverStatusLastChangedClockTick = StartingClockTick - 1
    /\  RegionLatestComputedTopology = [region \in Regions |-> NilComputedTopology]
    /\  RegionLastAppliedComputedTopologyTick = [region \in Regions |-> InvalidTick]
    /\  RegionCurrentTopologyConfigNumber = [region \in Regions |-> GlobalConfigNumber]
    /\  RegionCurrentTopologyUpsertIntent = [region \in Regions |-> TopologyIntentTypeNone]
    \*
    \* Regions will start in NOT heartbeating state so that they are immediately (i.e. in StartingClockTick)
    \* eligible to perform an UNGRACEFUL failover if write region doesn't heartbeat. This is an optimisation
    \* to reduce the number of ticks we need to add to the history to complete an UNGRACEFUL failover and
    \* verify the invariant 'WritesEnabledAtEndOfHistoryWhenRegionsSetIsStable'
    \*
    \* To do this, setting a value older than previous tick as last heartbeated tick for each region.
    \*
    /\  GlobalReportedRegionTick = [region \in Regions |-> StartingClockTick - 2]
    /\  GlobalReportedRegionLatestCommittedUptoLSN = [region \in Regions |-> InitialLSN]
    /\  GlobalReportedRegionCurrentServiceStatus = [region \in Regions |-> NotHeartbeating]
    /\  GlobalRegionTargetServiceStatus = [region \in Regions |-> NotHeartbeating]
    /\  GlobalRegionCurrentGlobalConfigNumber = [region \in Regions |-> 1]
    /\  IsPreferredWriteRegionChangedInCurrentTick = FALSE
    /\  RegionStateHistory = <<>>
    /\  RegionCommittedDataAtLSN = [
            region \in Regions |-> 
                [
                    lsn \in LSNType |-> 
                        IF lsn = InitialLSN
                        THEN InitialWrittenDataValue
                        ELSE InvalidDataValue
                ]
        ]

\* ============================
\*      Misc. Helpers
\* ============================
\*
\* Shorthands for UNCHANGED variable groups
\*
GlobalStateVariables == <<
    GlobalCurrentWriteRegion,
    GlobalPreferredWriteRegion,
    GlobalFailoverStatus,
    GlobalConfigNumber,
    GlobalRegionTargetServiceStatus,
    GlobalFailoverStatusLastChangedClockTick >>

GlobalRegionStateVariables == <<
    GlobalReportedRegionTick,
    GlobalReportedRegionLatestCommittedUptoLSN,
    GlobalReportedRegionCurrentServiceStatus,
    GlobalRegionCurrentGlobalConfigNumber >>

RegionStateControlVariables == <<
    RegionCurrentServiceStatus,
    RegionCurrentBuildStatus,
    RegionLatestComputedTopology, 
    RegionLastAppliedComputedTopologyTick,
    RegionCurrentTopologyConfigNumber,
    RegionCurrentTopologyUpsertIntent >>

RegionStateDataVariables == <<
    RegionLatestCommittedUptoLSN,
    RegionCommittedDataAtLSN,
    RegionGCLSN >>

RegionStateVariables == <<
    RegionStateDataVariables,
    RegionStateControlVariables >>

MiscVariables == << 
    LastReadData,
    RegionStateHistory,
    NextDataToWrite,
    CurrentClockTick,
    IsPreferredWriteRegionChangedInCurrentTick >>

ReportOneRegionStateAndComputeTopologyVariables == <<
    RegionStateHistory, 
    NextDataToWrite, 
    LastReadData, 
    GlobalPreferredWriteRegion, 
    RegionLastAppliedComputedTopologyTick,
    CurrentClockTick, 
    IsPreferredWriteRegionChangedInCurrentTick, 
    RegionCurrentTopologyConfigNumber,
    RegionCurrentTopologyUpsertIntent, 
    RegionStateDataVariables,
    RegionCurrentBuildStatus,
    RegionCurrentServiceStatus >>

\* ==============================
\*      Client Reads & Writes
\* ==============================

\*
\* NOTE: 
\*      1.  All the variables prefixed with 'Global' are stored in global state store.
\*          Accessing global state store on any region for client operations is 
\*          unimplementable. So, all the client operation related actions look at
\*          region's local status instead.
\*      2.  The model only allows writes/reads on one document and all the LSNs
\*          represent increasing updates on the content of the same document
\*

\*  This models a client performing a write to the document in the database
\*  Write is first committed on the region, and then replicated to other regions.
WriteDataOnRegion(region) ==
    \* The below line consults the region's local status to allow 
    \* a client write to be served. This could be achieved by checking
    \* local primary's 'write' status.
    /\  RegionCurrentServiceStatus[region] = ReadWrite
    \* The below is always true if region has 'ReadWrite' status. (See ApplyComputedTopologyOnRegion)
    \* but, keeping the statement for clarity in understanding.
    /\  RegionCurrentBuildStatus[region] = BuildCompleted
    \* Increment the local LSN
    /\  \E lsn \in LSNType :
        /\  lsn = RegionLatestCommittedUptoLSN[region] + 1
        /\  RegionLatestCommittedUptoLSN' = [RegionLatestCommittedUptoLSN EXCEPT ![region] = lsn]
        /\  RegionCommittedDataAtLSN' = [
                RegionCommittedDataAtLSN EXCEPT
                ![region] = [
                    RegionCommittedDataAtLSN[region] EXCEPT ![lsn] = NextDataToWrite
                ]
            ]
    \* Generate a unique monotonically increasing data value 
    \* for the next write
    /\  NextDataToWrite' = NextDataToWrite + 1
    /\  UNCHANGED <<
            GlobalStateVariables,
            GlobalRegionStateVariables,
            RegionGCLSN,
            RegionStateControlVariables,
            LastReadData,
            RegionStateHistory,
            CurrentClockTick,
            IsPreferredWriteRegionChangedInCurrentTick >>

\* Changes/populates intent in topology stored on a region
\* ChangeTopologyIntent action can be only performed on a region with current status ReadWrite 
\* In implementation, this action will be invoked by control plane 
ChangeTopologyIntent(region) ==
    /\  RegionCurrentServiceStatus[region] = ReadWrite
    \* The below is always true if region has 'ReadWrite' status. (See ApplyComputedTopologyOnRegion)
    \* but, keeping the statement for clarity in understanding.
    /\  RegionCurrentBuildStatus[region] = BuildCompleted
    /\  \E topologyIntent \in TopologyIntentType :
        /\  RegionCurrentTopologyUpsertIntent' = [RegionCurrentTopologyUpsertIntent EXCEPT ![region] = topologyIntent]
    /\  UNCHANGED <<
            GlobalStateVariables,
            GlobalRegionStateVariables,
            RegionCurrentServiceStatus,
            RegionCurrentBuildStatus,
            RegionCurrentTopologyConfigNumber,
            RegionLatestComputedTopology, 
            RegionLastAppliedComputedTopologyTick,
            RegionStateDataVariables,
            RegionStateHistory,
            NextDataToWrite,
            CurrentClockTick,
            IsPreferredWriteRegionChangedInCurrentTick,
            LastReadData >>

\* Read models a client performing a read on the document in the database
ReadDataOnRegion(region) ==
    /\  
        \/  RegionCurrentServiceStatus[region] = ReadOnlyReplicationAllowed
        \/  RegionCurrentServiceStatus[region] = ReadOnlyReplicationDisallowed
        \/  RegionCurrentServiceStatus[region] = ReadWrite
        \/  RegionCurrentServiceStatus[region] = ReadWriteWithWritesQuiesced
    \* The below is always true if region has 'ReadWrite' status. (See ApplyComputedTopologyOnRegion)
    /\  RegionCurrentBuildStatus[region] = BuildCompleted
    \* Only read globally committed data
    /\  RegionLatestCommittedUptoLSN[region] = RegionGCLSN[region]
    /\  LastReadData' = [Region |-> region, Data |-> RegionCommittedDataAtLSN[region][RegionLatestCommittedUptoLSN[region]]]
    /\  UNCHANGED << 
            GlobalStateVariables,
            GlobalRegionStateVariables,
            RegionStateVariables,
            RegionStateHistory,
            NextDataToWrite,
            CurrentClockTick,
            IsPreferredWriteRegionChangedInCurrentTick >>

\* This action replicates one LSN from the current write region or a non-heartbeating region
\* to one of the read regions in the same configuration
ReplicateDataToOneRegion(sourceRegion) ==
    /\
        \/  RegionCurrentServiceStatus[sourceRegion] = ReadWrite
        \/  RegionCurrentServiceStatus[sourceRegion] = ReadWriteWithWritesQuiesced
        \* Not heartbeating write region's replicas could still try to replicate
        \/  RegionCurrentServiceStatus[sourceRegion] = NotHeartbeating
    /\  \E targetRegion \in Regions:
        /\  targetRegion # sourceRegion
        /\  RegionCurrentServiceStatus[targetRegion] = ReadOnlyReplicationAllowed
        /\  RegionCurrentTopologyConfigNumber[targetRegion] = RegionCurrentTopologyConfigNumber[sourceRegion]
        /\  RegionLatestCommittedUptoLSN[targetRegion] < RegionLatestCommittedUptoLSN[sourceRegion]
        /\  LET NextLSNToReplicate == RegionLatestCommittedUptoLSN[targetRegion] + 1
            IN
                /\  RegionLatestCommittedUptoLSN' = [RegionLatestCommittedUptoLSN EXCEPT ![targetRegion] = NextLSNToReplicate]
                /\  RegionCommittedDataAtLSN' = [
                        RegionCommittedDataAtLSN EXCEPT 
                        ![targetRegion] = [
                            RegionCommittedDataAtLSN[targetRegion] EXCEPT 
                                ![NextLSNToReplicate] = RegionCommittedDataAtLSN[sourceRegion][NextLSNToReplicate]
                        ]
                    ]
    /\  UNCHANGED << 
            GlobalStateVariables,
            GlobalRegionStateVariables,
            MiscVariables,
            RegionGCLSN,
            RegionStateControlVariables >>

AdvanceGCLSNOnRegion(writeRegion) ==
    LET 
        \* Alive regions represent all the regions that are NOT in the dead i.e. not NotHeartbeating state
        \* If a region is in NotHeartbeating, and when it comes
        \* back up alive, it will perform a reseed with current write region
        \* to ensure that GCLSN is upto date on that region. so, if a read region 
        \* is dead, then it is NOT considered for advancing GCLSN on the write region
        aliveRegions == {
            region \in Regions: RegionCurrentServiceStatus[region] # NotHeartbeating
        }
    IN
    \* Global Committed LSN (GCLSN) can advance on a write region only if atleast a 
    \* majority region set is alive and write region is part of the set
    /\  Cardinality(aliveRegions) >= MajorityRegionsSetSize
    /\  
        \/  RegionCurrentServiceStatus[writeRegion] = ReadWrite
        \/  RegionCurrentServiceStatus[writeRegion] = ReadWriteWithWritesQuiesced
    /\  RegionCurrentBuildStatus[writeRegion] = BuildCompleted
    \* Pick a LSN that is committed on all alive regions
    /\  \E GCLSN \in LSNType:
        /\  GCLSN >= RegionGCLSN[writeRegion]
        /\  \A otherRegion \in aliveRegions:
            /\  
                \/  RegionCurrentServiceStatus[otherRegion] = ReadWrite
                \/  RegionCurrentServiceStatus[otherRegion] = ReadWriteWithWritesQuiesced
                \/  RegionCurrentServiceStatus[otherRegion] = ReadOnlyReplicationAllowed
            /\  RegionCurrentBuildStatus[otherRegion] = BuildCompleted
            /\  GCLSN <= RegionLatestCommittedUptoLSN[otherRegion]
        /\  RegionGCLSN' = [RegionGCLSN EXCEPT ![writeRegion] = GCLSN]
    /\  UNCHANGED << 
            GlobalStateVariables,
            GlobalRegionStateVariables,
            MiscVariables,
            RegionLatestCommittedUptoLSN,
            RegionCommittedDataAtLSN,
            RegionStateControlVariables >>

ReplicateGCLSNFromRegion(sourceRegion) ==
    /\
        \/  RegionCurrentServiceStatus[sourceRegion] = ReadWrite
        \/  RegionCurrentServiceStatus[sourceRegion] = ReadWriteWithWritesQuiesced
        \* Not heartbeating write region's replicas could still try to replicate
        \/  RegionCurrentServiceStatus[sourceRegion] = NotHeartbeating
    /\  \E targetRegion \in Regions:
        /\  targetRegion # sourceRegion
        \* In bound replication must be allowed on the read region
        /\  RegionCurrentServiceStatus[targetRegion] = ReadOnlyReplicationAllowed
        /\  RegionCurrentTopologyConfigNumber[targetRegion] = RegionCurrentTopologyConfigNumber[sourceRegion]
        /\  RegionGCLSN' = [RegionGCLSN EXCEPT ![targetRegion] = RegionGCLSN[sourceRegion]]
    /\  UNCHANGED << 
            GlobalStateVariables,
            GlobalRegionStateVariables,
            MiscVariables,
            RegionLatestCommittedUptoLSN,
            RegionCommittedDataAtLSN,
            RegionStateControlVariables >>

UserChangesGlobalPreferredWriteRegion ==
    /\  GlobalPreferredWriteRegion' \in Regions
    /\  IsPreferredWriteRegionChangedInCurrentTick' = TRUE
    /\  UNCHANGED <<
            GlobalCurrentWriteRegion,
            GlobalFailoverStatus,
            GlobalConfigNumber,
            GlobalFailoverStatusLastChangedClockTick,
            GlobalRegionTargetServiceStatus,
            GlobalRegionStateVariables,
            RegionStateVariables,
            LastReadData,
            RegionStateHistory,
            NextDataToWrite,
            CurrentClockTick >>

\* ============================
\*      Global State Helpers
\* ============================

\* Declare a region is not heartbeating only if it has not heartbeated at the last tick
\* Current tick is still in progress, so do not declare prematurely that a region has not
\* heartbeated
IsRegionHeartbeating(region) ==
    /\  ((CurrentClockTick - GlobalReportedRegionTick'[region]) <= NumberOfTicksToDeclareRegionAsDead)

AdvanceGlobalConfigNumber ==
    /\  GlobalConfigNumber' \in ConfigNumberType
    /\  GlobalConfigNumber' = GlobalConfigNumber + 1

IsRegionOnCurrentGlobalConfiguration(region) ==
    \* Need to check the next state for this variable since it could've changed as part of the current action that IsRegionOnCurrentGlobalConfiguration is composed into
    /\  GlobalRegionCurrentGlobalConfigNumber'[region] = GlobalConfigNumber

IsCurrentWriteRegionOnCurrentGlobalConfiguration ==
    /\  IsRegionOnCurrentGlobalConfiguration(GlobalCurrentWriteRegion)

IsPreferredWriteRegionOnCurrentGlobalConfiguration ==
    /\  IsRegionOnCurrentGlobalConfiguration(GlobalPreferredWriteRegion)

\*
\* Some helpers for read/modifying failover status
\*
IsAnyFailoverInProgress(failoverStatus) == 
    /\  failoverStatus # NoFailoverInProgress

IsGracefulFailoverInProgressPrime ==
    /\  GlobalFailoverStatus' = GracefulFailoverInProgress

IsGracefulFailoverInProgress ==
    /\  GlobalFailoverStatus = GracefulFailoverInProgress

IsWriteStatusRevokedByExternalSource ==
    /\  GlobalFailoverStatus = WriteStatusRevokedByExternalSource

IsWriteStatusRevokedByExternalSourcePrime ==
    /\  GlobalFailoverStatus' = WriteStatusRevokedByExternalSource

IsUngracefulFailoverInProgress ==
    /\  GlobalFailoverStatus = UngracefulFailoverInProgress

IsUngracefulFailoverInProgressPrime ==
    /\  GlobalFailoverStatus' = UngracefulFailoverInProgress

SetFailoverStatusToGraceful == 
    /\  GlobalFailoverStatus' = GracefulFailoverInProgress
    /\  GlobalFailoverStatusLastChangedClockTick' = CurrentClockTick
    /\  AdvanceGlobalConfigNumber

SetFailoverStatusToWriteStatusRevokedByExternalSource== 
    /\  GlobalFailoverStatus' = WriteStatusRevokedByExternalSource
    /\  GlobalFailoverStatusLastChangedClockTick' = CurrentClockTick
    /\  AdvanceGlobalConfigNumber

SetFailoverStatusToUngraceful == 
    /\  GlobalFailoverStatus' = UngracefulFailoverInProgress
    /\  GlobalFailoverStatusLastChangedClockTick' = CurrentClockTick
    /\  AdvanceGlobalConfigNumber

SetFailoverStatusToNone == 
    /\  GlobalFailoverStatus' = NoFailoverInProgress
    /\  GlobalFailoverStatusLastChangedClockTick' = CurrentClockTick
    /\  AdvanceGlobalConfigNumber

IsGracefulFailoverTimedOut ==
    /\  (CurrentClockTick - GlobalFailoverStatusLastChangedClockTick) >= GracefulFailoverExpirationTicks

HasTopologyIntentToRevokeGlobalWriteStatus(region) == 
    /\ RegionCurrentTopologyUpsertIntent[region] = TopologyIntentTypeRevokeGlobalWriteStatus

HasTopologyIntentToGrantGlobalWriteStatus(region) == 
    /\ RegionCurrentTopologyUpsertIntent[region] = TopologyIntentTypeGrantGlobalWriteStatus

HasTopologyIntentToIncrementGlobalConfigurationNumber(region) == 
    /\ RegionCurrentTopologyUpsertIntent[region] = TopologyIntentTypeIncrementGlobalConfigurationNumber

CanRevokeGlobalWriteStatusByExternalSource ==
    /\ 
        \/  ~IsAnyFailoverInProgress(GlobalFailoverStatus)
        \* If Graceful FailoverInProgress then RevokeWriteStatusByExternalSource has higher priority
        \/  IsGracefulFailoverInProgress
    /\  \E writeRegion \in Regions:
        \* Ensuring only topology received on current write region will be honored
        /\  writeRegion = GlobalCurrentWriteRegion
        /\  HasTopologyIntentToRevokeGlobalWriteStatus(GlobalCurrentWriteRegion)

RevokeGlobalWriteStatusByExternalSource == 
    /\  SetFailoverStatusToWriteStatusRevokedByExternalSource
    /\  UNCHANGED << GlobalCurrentWriteRegion >>

CanRollbackRevokeGlobalWriteStatusByExternalSource ==
    /\  IsWriteStatusRevokedByExternalSource
    /\    
        \* if topology intent says GrantGlobalWriteStatus, then just rollback RevokeGlobalWriteStatusByExternalSource 
        \/  HasTopologyIntentToGrantGlobalWriteStatus(GlobalCurrentWriteRegion)
        \* Might need to use different configuration for this timeout
        \* This has been added to handle the cases, if external sources missed to sent the intent GrantGlobalWriteStatus
        \/  IsGracefulFailoverTimedOut

RollbackRevokeGlobalWriteStatusByExternalSource == 
    /\  SetFailoverStatusToNone
    /\  UNCHANGED << GlobalCurrentWriteRegion >>
\* ============================
\*      Graceful Failover
\* ============================
CanInitiateGracefulFailover ==
    /\  ~IsAnyFailoverInProgress(GlobalFailoverStatus)
    /\  IsCurrentWriteRegionOnCurrentGlobalConfiguration
    /\  IsRegionHeartbeating(GlobalCurrentWriteRegion)
    /\  IsPreferredWriteRegionOnCurrentGlobalConfiguration
    /\  IsRegionHeartbeating(GlobalPreferredWriteRegion)
    /\  GlobalPreferredWriteRegion # GlobalCurrentWriteRegion

InitiateGracefulFailover ==
    /\  SetFailoverStatusToGraceful
    /\  UNCHANGED << GlobalCurrentWriteRegion >>

\* Check if the Preferred Write Region has caught up with the Current
\* Write Region
IsLSNCatchupCompleteOnPreferredWriteRegion ==
    \* Need to check the next state for these variable since they could've changed as part of the current action that IsLSNCatchupCompleteOnPreferredWriteRegion is composed into
    /\  GlobalReportedRegionLatestCommittedUptoLSN'[GlobalPreferredWriteRegion] = GlobalReportedRegionLatestCommittedUptoLSN'[GlobalCurrentWriteRegion]

CanCompleteGracefulFailover ==
    /\  IsGracefulFailoverInProgress
    /\  IsCurrentWriteRegionOnCurrentGlobalConfiguration
    /\  IsPreferredWriteRegionOnCurrentGlobalConfiguration
    \* Current write region need not heartbeat for graceful
    \* failover to complete, as long as the preferred write
    \* has caught up with it.
    /\  IsRegionHeartbeating(GlobalPreferredWriteRegion)
    /\  GlobalPreferredWriteRegion # GlobalCurrentWriteRegion
    \* When both current write region and preferred write region have reached this global configuration, 
    \* they MUST have stopped their writes and have reported their latest committed LSN to the global state. 
    \* The following line ensures the comitted LSN has caught up on preferred write region.
    /\  IsLSNCatchupCompleteOnPreferredWriteRegion

CompleteGracefulFailover ==
    /\  GlobalCurrentWriteRegion' = GlobalPreferredWriteRegion
    /\  SetFailoverStatusToNone

CanRecallInProgressGracefulFailover ==
    /\  IsGracefulFailoverInProgress
    /\    
        \/  GlobalPreferredWriteRegion = GlobalCurrentWriteRegion
        \/  ~IsRegionHeartbeating(GlobalPreferredWriteRegion)
        \/  IsGracefulFailoverTimedOut

RecallInProgressGracefulFailover ==
    /\  SetFailoverStatusToNone
    /\  UNCHANGED << GlobalCurrentWriteRegion >>

\* ============================
\*      Ungraceful Failover
\* ============================

\* Heartbeating regions can never be an empty set
\* since the region reporting/performing state
\* update must be present in the the list as it
\* is currently heartbeating
HeartbeatingRegions == {
    region \in Regions:
    /\  IsRegionHeartbeating(region)
}

ChooseRegionWithHighestProgressAsCurrentWriteRegion ==
    \E candidateWriteRegion \in HeartbeatingRegions:
    /\  \A otherRegion \in HeartbeatingRegions:
        /\  IsRegionOnCurrentGlobalConfiguration(candidateWriteRegion)
        /\  IsRegionOnCurrentGlobalConfiguration(otherRegion)
        \* The current action is part of ReportOneRegionStateAndComputeTopology which executes an action to change GlobalReportedRegionLatestCommittedUptoLSN
        \* prior to the invocation of this action. As a result, we need to check the next (primed) state for these variables
        /\  GlobalReportedRegionLatestCommittedUptoLSN'[candidateWriteRegion] 
                >= GlobalReportedRegionLatestCommittedUptoLSN'[otherRegion]
    /\  GlobalCurrentWriteRegion' = candidateWriteRegion

AreAllHeartbeatingRegionsOnCurrentConfiguration ==
    /\  \A region \in HeartbeatingRegions:
        /\  IsRegionOnCurrentGlobalConfiguration(region)

CanCompleteUngracefulFailover ==
    /\  AreAllHeartbeatingRegionsOnCurrentConfiguration
    \* This condition is required for strong consistency read property in the model.
    \* Otherwise, in a 3 region setup, where the write quorum is 2 regions, and both
    \* regions in the write quorum fail, failover could still happen to the region not
    \* in quorum leading to data loss.
    /\  Cardinality(HeartbeatingRegions) >= MajorityRegionsSetSize
    /\  IsUngracefulFailoverInProgress

CompleteUngracefulFailover ==
    /\  ChooseRegionWithHighestProgressAsCurrentWriteRegion
    /\  SetFailoverStatusToNone

CanInitiateUngracefulFailover ==
    /\  ~IsAnyFailoverInProgress(GlobalFailoverStatus)
    /\  ~IsRegionHeartbeating(GlobalCurrentWriteRegion)

InitiateUngracefulFailover ==
    /\  SetFailoverStatusToUngraceful
    /\  UNCHANGED << GlobalCurrentWriteRegion >>

IsCurrentWriteRegionAvailableForReseed ==
    \/  RegionCurrentServiceStatus[GlobalCurrentWriteRegion] = ReadWrite
    \/  RegionCurrentServiceStatus[GlobalCurrentWriteRegion] = ReadWriteWithWritesQuiesced

\* ==============================================================
\*      Region Report, Topology Computation & Application
\* ==============================================================

IsRegionBuilt(region) ==
    RegionCurrentBuildStatus[region] = BuildCompleted

IsWriteRegionServiceStatus(status) ==
    \/  status = ReadWrite
    \/  status = ReadWriteWithWritesQuiesced

RegionHasWriteServiceStatus(region) ==
    IsWriteRegionServiceStatus(RegionCurrentServiceStatus[region])

\* If the region's current status meets the required target
\* state set on the global state, then this global
\* configuration number/topology is known to be acknowledged
\* by this region
UpdateCurrentGlobalConfigurationForRegion(reportingRegion) ==
    \* If the target state is reached by this region, then acknowledge the configuration number
    \* by setting the region's ACK number in the global state to be the same as the current 
    \* global configuration number
    IF
        \*
        \* Region reaching NotHeartbeating state should NOT declare that it has
        \* reached the current global configuration, since the region
        \* might have crashed and coming back up alive and it needs to fetch and
        \* apply target state from global state, before it can be declared as reached
        \* current configuration
        \* "UpdateCurrentGlobalConfigurationForRegion is part of the action ReportRegionInformationToGLobalState,
        \*  which changes the GlobalReportedRegionCurrentServiceStatus for this region in the next state, which is why we are checking the 'primed' variables here'
        /\  GlobalReportedRegionCurrentServiceStatus'[reportingRegion] # NotHeartbeating
        /\  GlobalReportedRegionCurrentServiceStatus'[reportingRegion] = GlobalRegionTargetServiceStatus[reportingRegion]
    THEN 
        /\  GlobalRegionCurrentGlobalConfigNumber' = [GlobalRegionCurrentGlobalConfigNumber EXCEPT ![reportingRegion] = GlobalConfigNumber]
    ELSE
        \* Configuration number for this region is unchanged since it has not yet reached the
        \* global configuration
        /\  UNCHANGED << GlobalRegionCurrentGlobalConfigNumber >>

\* Region Reports 
\* => Current Region Service Status
\* => Current Committed Upto LSN
\* 
ReportRegionInformationToGlobalState(reportingRegion) ==
    /\  GlobalReportedRegionLatestCommittedUptoLSN' = [
            GlobalReportedRegionLatestCommittedUptoLSN 
                EXCEPT ![reportingRegion] = RegionLatestCommittedUptoLSN[reportingRegion]
        ]
    /\  GlobalReportedRegionCurrentServiceStatus' = [
            GlobalReportedRegionCurrentServiceStatus 
                EXCEPT ![reportingRegion] = RegionCurrentServiceStatus[reportingRegion]
        ]
    /\  GlobalReportedRegionTick' = [
            GlobalReportedRegionTick 
                EXCEPT ![reportingRegion] = CurrentClockTick
        ]
    /\  UpdateCurrentGlobalConfigurationForRegion(reportingRegion)

DoNoFailoverAction ==
    \* Handling Topology intent to incrementglobalcofigurationnumber
    IF
        /\  \E writeRegion \in Regions:
            \* Ensuring only topology received on current write region will be honored
            /\  writeRegion = GlobalCurrentWriteRegion
            /\  HasTopologyIntentToIncrementGlobalConfigurationNumber(GlobalCurrentWriteRegion)
    THEN 
        /\  AdvanceGlobalConfigNumber
        /\  UNCHANGED << GlobalCurrentWriteRegion, GlobalFailoverStatus, GlobalFailoverStatusLastChangedClockTick >> 
    ELSE 
        /\  UNCHANGED << GlobalCurrentWriteRegion, GlobalFailoverStatus, GlobalConfigNumber, GlobalFailoverStatusLastChangedClockTick >>

ComputeTargetStateForRegions ==
    /\  GlobalRegionTargetServiceStatus' = [
            region \in Regions |->
            IF
                /\  IsRegionHeartbeating(region)
                /\  GlobalCurrentWriteRegion' = region
            THEN
                IF IsWriteStatusRevokedByExternalSourcePrime
                THEN
                \* If write status is revoked by an external source, write region's client writes are disallowed 
                \* but replication to read regions can continue
                    ReadWriteWithWritesQuiesced
                ELSE IF
                    IsGracefulFailoverInProgressPrime
                THEN
                    \* GRACEFUL failover in progress, WRITE REGION's client writes are disallowed
                    \* but replication to read regions can continue.
                    ReadWriteWithWritesQuiesced
                ELSE IF 
                    IsUngracefulFailoverInProgressPrime
                THEN 
                    \* UNGRACEFUL failover in progress, WRITE REGION's client writes are disallowed
                    \* and also replication to read regions is disallowed
                    ReadOnlyReplicationDisallowed
                ELSE
                    \* NO failover in progress, WRITE REGION should allow accepting client writes
                    \* and also allowed to replicate to read regions
                    ReadWrite
            ELSE IF
                /\  IsRegionHeartbeating(region)
                /\  GlobalCurrentWriteRegion' # region
            THEN
                IF IsWriteStatusRevokedByExternalSourcePrime
                THEN
                    \* WriteStatusRevokedByExternalSource in progress, READ REGION can accept client reads and
                    \* also replication traffic from write region
                    ReadOnlyReplicationAllowed
                ELSE IF 
                    IsGracefulFailoverInProgressPrime
                THEN
                    \* GRACEFUL failover in progress, READ REGION can accept client reads and
                    \* also replication traffic from write region
                    ReadOnlyReplicationAllowed
                ELSE IF
                    IsUngracefulFailoverInProgressPrime
                THEN
                    \* UNGRACEFUL failover in progress, READ REGION can accept client reads but
                    \* not accept any replication traffic from previous write region
                    ReadOnlyReplicationDisallowed
                ELSE
                    \* NO failover in progress, read region must be able to accept client reads
                    \* and replication traffic
                    ReadOnlyReplicationAllowed
            ELSE
                \* Region is NOT heartbeating
                \* It must revoke it's lease with the failover manager
                NotHeartbeating
        ]

PerformFailover ==
    IF 
        CanRevokeGlobalWriteStatusByExternalSource
    THEN 
        RevokeGlobalWriteStatusByExternalSource
    ELSE IF
        CanRollbackRevokeGlobalWriteStatusByExternalSource
    THEN 
        RollbackRevokeGlobalWriteStatusByExternalSource
    ELSE IF  
        CanInitiateGracefulFailover
    THEN 
        InitiateGracefulFailover
    ELSE IF 
        CanCompleteGracefulFailover
    THEN 
        CompleteGracefulFailover
    ELSE IF 
        CanRecallInProgressGracefulFailover
    THEN 
        RecallInProgressGracefulFailover
    ELSE IF 
        CanInitiateUngracefulFailover
    THEN 
        InitiateUngracefulFailover
    ELSE IF 
        CanCompleteUngracefulFailover
    THEN 
        CompleteUngracefulFailover
    ELSE 
        DoNoFailoverAction

\*
\* Perform topology computation
\* As part of topology computation, first a failover is
\* performed (if any), and then the target state for
\* each region is computed on the global state
\*
PerformTopologyComputation ==
    /\  PerformFailover
    /\  ComputeTargetStateForRegions

\* Downloads the computed topology from the global state 
\* to the region that initiated the topology computation
ObtainComputedTopologyForRegion(computingRegion) ==
    /\  RegionLatestComputedTopology' = [
            RegionLatestComputedTopology 
                EXCEPT ![computingRegion] = [
                    TargetServiceStatus |-> GlobalRegionTargetServiceStatus'[computingRegion],
                    ConfigNumber |-> GlobalConfigNumber'
                ]
        ]

\* Build is complete copy of data from the beginning of time to the latest committed LSN on the write region
PerformBuildOnRegion(region, writeRegion) ==
    /\  RegionLatestCommittedUptoLSN' = [RegionLatestCommittedUptoLSN EXCEPT ![region] = RegionLatestCommittedUptoLSN[writeRegion]]
    /\  RegionCommittedDataAtLSN' = [RegionCommittedDataAtLSN EXCEPT ![region] = RegionCommittedDataAtLSN[writeRegion]]
    /\  RegionGCLSN' = [RegionGCLSN EXCEPT ![region] = RegionGCLSN[writeRegion]]

\* ReadyForBuild -> BuildCompleted
\* This requires the write region to be available.
ReadRegionBuildsDataFromWriteRegion(region) ==
    \*  ReadOnlyReplicationDisallowed state is not allowed for performing
    \*  builds since the read region has disconnected its link with 
    \*  the write region.
    /\  RegionCurrentServiceStatus[region] = ReadOnlyReplicationAllowed
    /\  RegionCurrentBuildStatus[region] = ReadyForBuild
    \*  NOTE:
    \*  Not modelling false progress detection here. Check the
    \* 'AtomicReseed.tla' for more details on reseed modelling
    \*  and conditions to detect false progress.
    \*  Instead, we require the region to go through a 
    \*  ReadyForBuild -> BuildCompleted state, directly.
    \*
    /\  \E writeRegion \in Regions:
        /\  RegionHasWriteServiceStatus(writeRegion)
        /\  IsRegionBuilt(writeRegion)
        /\  PerformBuildOnRegion(region, writeRegion)
    /\  RegionCurrentBuildStatus' = [
            RegionCurrentBuildStatus
                EXCEPT ![region] = BuildCompleted
        ]
    /\  UNCHANGED <<
            RegionCurrentTopologyConfigNumber,
            RegionCurrentTopologyUpsertIntent,
            RegionLastAppliedComputedTopologyTick,
            GlobalStateVariables,
            RegionCurrentServiceStatus,
            GlobalRegionStateVariables,
            RegionLatestComputedTopology,
            MiscVariables >>

\* Report a single region's local state to the global state
\* Global state performs a topology computation as part
\* of the report, and returns the computed topology back
\* to the region. The region then applies the returned topology
\* on it's local state via. action 'ApplyComputedTopologyOnRegion'
ReportOneRegionStateAndComputeTopology(region) ==
    /\  ReportRegionInformationToGlobalState(region)
    /\  PerformTopologyComputation
    /\  ObtainComputedTopologyForRegion(region)
    /\  UNCHANGED << ReportOneRegionStateAndComputeTopologyVariables >>

ReportOneRegionStateAndComputeTopologyIfNotReportedInCurrentTick(region) ==
    \* The below accesses global state to check if it has reported in the current tick.
    \* This action is not what we implemented but it exists solely for quickly verifiying 
    \* the properties of the specification without having to run through a lot of state space.
    \* See the action 'ReportOneRegionStateAndComputeTopology' which is the action in the spec 
    \* that we have implemented.
    /\  GlobalReportedRegionTick[region] # CurrentClockTick
    /\  ReportRegionInformationToGlobalState(region)
    /\  PerformTopologyComputation
    /\  ObtainComputedTopologyForRegion(region)
    /\  UNCHANGED << ReportOneRegionStateAndComputeTopologyVariables >>

HasRegionJustAcquiredReadWriteStatus(region) ==
    /\  RegionCurrentServiceStatus[region] # ReadWrite
    /\  RegionCurrentServiceStatus'[region] = ReadWrite

ResetLatestComputedTopologyToNilOnRegion(region) ==
    /\  RegionLatestComputedTopology' = [RegionLatestComputedTopology EXCEPT ![region] = NilComputedTopology]

\*
\* Applies the latest computed and downloaded topology on one region
\*
ApplyComputedTopologyOnRegion(region) ==
    LET computedTopology == RegionLatestComputedTopology[region]
    IN  /\  computedTopology # NilComputedTopology
        /\  RegionCurrentServiceStatus' = [RegionCurrentServiceStatus EXCEPT ![region] = computedTopology.TargetServiceStatus]
        /\  RegionCurrentTopologyConfigNumber' = [RegionCurrentTopologyConfigNumber EXCEPT ![region] = computedTopology.ConfigNumber]
        \* Topology Upsert intent from external sources will be removed when computed topology is applied on the region
        /\  RegionCurrentTopologyUpsertIntent' = [RegionCurrentTopologyUpsertIntent EXCEPT ![region] = TopologyIntentTypeNone]
        /\  RegionLastAppliedComputedTopologyTick' = [RegionLastAppliedComputedTopologyTick EXCEPT ![region] = CurrentClockTick]
        \* If a region acquired write status and has just come up, it assumes its data is correct 
        \* and does not attempt to rebuild from another source. So it transitions to BuildCompleted.
        /\  IF HasRegionJustAcquiredReadWriteStatus(region)
            THEN RegionCurrentBuildStatus' = [RegionCurrentBuildStatus EXCEPT ![region] = BuildCompleted]
            ELSE UNCHANGED <<RegionCurrentBuildStatus>>
        /\  ResetLatestComputedTopologyToNilOnRegion(region)
        /\  UNCHANGED <<
                GlobalStateVariables,
                GlobalRegionStateVariables,
                MiscVariables,
                RegionStateDataVariables >>

\* ============================
\*      Global Time Related
\* ============================

HasRegionHeartbeatedWithGlobalStateAtClockTick(region, clockTick) ==
    /\  GlobalReportedRegionTick[region] = clockTick

HasRegionAppliedComputedTopologyAtClockTick(region, clockTick) ==
    /\  RegionLastAppliedComputedTopologyTick[region] = clockTick

\*
\* If global state determines that a region has not hearbeated for a certain amount of time
\* (or) the region is unable to apply the latest computed topology, then it declares the region 
\* as dead by forcefully setting the respective region's status to NotHeartbeating. 
\* This is analogous to how a region self-terminates if it cannot renew its lease with the 
\* global state every clock tick. This is to ensure that the region is disallowed from serving
\* any stale reads to the clients.
\*
TerminateDeadRegionsDuringClockTick(previousClockTick) ==
    LET
        heartbeatedAndTopologyAppliedRegions == {
            region \in Regions:
            /\  HasRegionHeartbeatedWithGlobalStateAtClockTick(region, previousClockTick)
            /\  HasRegionAppliedComputedTopologyAtClockTick(region, previousClockTick)
        }
    IN
        /\  RegionCurrentServiceStatus' = [
                region \in Regions |->
                    IF region \in heartbeatedAndTopologyAppliedRegions
                    THEN RegionCurrentServiceStatus[region]
                    ELSE InitialServiceStatus
            ]
        \* Region requires a build if it has gone down in a tick
        \* since the other regions would have made progress. Since we do not
        \* model false progress detection in this spec, we always
        \* perform build if the region has gone down. If the region has not
        \* gone down, then it must be part of the write quorum, so it does 
        \* not need a build. Note that, this spec doesn't allow read regions
        \* to acquire false progress while they are part of write quorum since
        \* the writes are always committed on the write region first, and then
        \* replicated to read regions. So, ReadyForBuild is needed only if region
        \* has gone down.
        /\  RegionCurrentBuildStatus' = [
                region \in Regions |->
                    IF region \in heartbeatedAndTopologyAppliedRegions
                    THEN RegionCurrentBuildStatus[region]
                    ELSE ReadyForBuild
            ]

ResetComputedTopologyToNilOnAllRegions ==
    \* Reset to NilComputedTopology on all regions to disallow topology applications
    \* in the current tick for the computed topologies in the previous tick.
    RegionLatestComputedTopology' = [region \in Regions |-> NilComputedTopology]

\* Clock tick models how time in progressed in the system. Time
\* progresses monotonically with increments of 1 tick.
\* For each clock tick, all regions will try to perform heartbeat
\* with their current status to the global state.
AdvanceCurrentClockTick ==
    /\  CurrentClockTick' \in TickType
    /\  CurrentClockTick' = CurrentClockTick + 1
    /\  LET previousClockTick == CurrentClockTick
        IN
            /\  ResetComputedTopologyToNilOnAllRegions
            /\  TerminateDeadRegionsDuringClockTick(previousClockTick)
            \* The below is not implementable in a real system since advancing time doesn't have
            \* access to global state, but this is only used to verifying an invariant, so it is okay
            \* to do so here.
            /\  RegionStateHistory' = Append(RegionStateHistory,
                [
                    currentWriteRegion |-> GlobalCurrentWriteRegion, 
                    isPreferredWriteRegionChanged |-> IsPreferredWriteRegionChangedInCurrentTick,
                    failoverStatus |-> GlobalFailoverStatus,
                    aliveRegions |-> {
                        \* Region is considered 'alive' if it heartbeated and applied topology 
                        \* in the previous tick.
                        region \in Regions:
                            /\  HasRegionHeartbeatedWithGlobalStateAtClockTick(region, previousClockTick)
                            /\  HasRegionAppliedComputedTopologyAtClockTick(region, previousClockTick)
                    },
                    deadRegions |-> {
                        \* Region is considered 'dead' if it didn't heartbeat and also didn't apply any
                        \* topology in previous tick
                        \*
                        \* NOTE:
                        \*      ~HasRegionHeartbeatedWithGlobalStateAtClockTick(region)
                        \*      HasRegionAppliedComputedTopologyAtClockTick(region)
                        \*
                        \*      (or)
                        \*
                        \*      HasRegionHeartbeatedWithGlobalStateAtClockTick(region)
                        \*      ~HasRegionAppliedComputedTopologyAtClockTick(region)
                        \*
                        \*      cases are not considered 'dead'. Since in these, the region is not in 
                        \*      a stable state for the invariant check 'WritesEnabledAtEndOfHistoryWhenRegionsSetIsStable'
                        \*
                        region \in Regions:
                            /\  ~HasRegionHeartbeatedWithGlobalStateAtClockTick(region, previousClockTick)
                            /\  ~HasRegionAppliedComputedTopologyAtClockTick(region, previousClockTick)
                    }
                ])
    \* Reset it back to FALSE for the next tick
    /\  IsPreferredWriteRegionChangedInCurrentTick' = FALSE
    /\  UNCHANGED <<
            GlobalStateVariables,
            GlobalRegionStateVariables,
            RegionStateDataVariables,
            RegionLastAppliedComputedTopologyTick,
            RegionCurrentTopologyConfigNumber,
            RegionCurrentTopologyUpsertIntent,
            LastReadData,
            NextDataToWrite >>

\* ============================
\*      Next
\* ============================

Next ==
    \* 'UserChangesGlobalPreferredWriteRegion' may have some action restrictions, check the model.
    \/  UserChangesGlobalPreferredWriteRegion
    \/  AdvanceCurrentClockTick
    \/  \E region \in Regions:
        \/  WriteDataOnRegion(region)
        \/  ReadDataOnRegion(region)
        \/  ReplicateDataToOneRegion(region)
        \/  ChangeTopologyIntent(region)
        \/  AdvanceGCLSNOnRegion(region)
        \/  ReplicateGCLSNFromRegion(region)
        \/  ReportOneRegionStateAndComputeTopology(region)
        \/  ApplyComputedTopologyOnRegion(region)
        \/  ReadRegionBuildsDataFromWriteRegion(region)

\* This is an optimisation only for quick model verification purposes.
\* This spec limits the number of reports done by a region per tick to atmost 1.
\* (only change compared to 'Next' is 'ReportOneRegionStateAndComputeTopologyIfNotReportedInCurrentTick')
NextAtmostOneRegionReportPerTick ==
    \* 'UserChangesGlobalPreferredWriteRegion' may have some action restrictions, check the model.
    \/  UserChangesGlobalPreferredWriteRegion
    \/  AdvanceCurrentClockTick
    \/  \E region \in Regions:
        \/  WriteDataOnRegion(region)
        \/  ReadDataOnRegion(region)
        \/  ReplicateDataToOneRegion(region)
        \/  ChangeTopologyIntent(region)
        \/  AdvanceGCLSNOnRegion(region)
        \/  ReplicateGCLSNFromRegion(region)
        \/  ReportOneRegionStateAndComputeTopologyIfNotReportedInCurrentTick(region)
        \/  ApplyComputedTopologyOnRegion(region)
        \/  ReadRegionBuildsDataFromWriteRegion(region)

\* ============================
\*      Invariants
\* ============================

TypeOK ==
    /\  LastReadData \in LastReadDataType
    /\  RegionLatestCommittedUptoLSN \in [Regions -> LSNType]
    /\  RegionGCLSN \in [Regions -> LSNType]
    /\  RegionCurrentServiceStatus \in [Regions -> RegionServiceStatusType]
    /\  RegionCurrentBuildStatus \in [Regions -> RegionBuildStatusType]
    /\  RegionLatestComputedTopology \in [Regions -> ComputedTopologyType]
    /\  RegionCurrentTopologyConfigNumber \in [Regions -> ConfigNumberType]
    /\  RegionCurrentTopologyUpsertIntent \in [Regions -> TopologyIntentType]
    /\  GlobalCurrentWriteRegion \in Regions
    /\  GlobalPreferredWriteRegion \in Regions
    /\  GlobalFailoverStatus \in GlobalFailoverStatusType
    /\  GlobalConfigNumber \in ConfigNumberType
    /\  CurrentClockTick \in TickType
    /\  GlobalFailoverStatusLastChangedClockTick \in TickType
    /\  GlobalReportedRegionTick \in [Regions -> TickType]
    /\  GlobalReportedRegionLatestCommittedUptoLSN \in [Regions -> LSNType]
    /\  GlobalReportedRegionCurrentServiceStatus \in [Regions -> RegionServiceStatusType]
    /\  GlobalRegionTargetServiceStatus \in [Regions -> RegionServiceStatusType]
    /\  GlobalRegionCurrentGlobalConfigNumber \in [Regions -> ConfigNumberType]
    /\  NextDataToWrite \in NextDataToWriteType
    /\  RegionCommittedDataAtLSN \in RegionLSNDataType
    /\  IsPreferredWriteRegionChangedInCurrentTick \in BOOLEAN
    /\  RegionLastAppliedComputedTopologyTick \in [Regions -> TickType \union {InvalidTick}]

IsRegionSetStableInHistory(recentHistoryEntries) ==
    LET
        lastRecentHistoryEntry == recentHistoryEntries[Len(recentHistoryEntries)]
    IN
        /\  \A index \in 1..Len(recentHistoryEntries):
            \* Alive regions set is the same throughout the history
            /\  recentHistoryEntries[index].aliveRegions = lastRecentHistoryEntry.aliveRegions
            \* Alive regions set is a majority throughout the history
            /\  Cardinality(recentHistoryEntries[index].aliveRegions) >= MajorityRegionsSetSize
            \*
            \* There is no region that is neither dead nor alive i.e. a region
            \* which has heartbeated but not applied topology in this tick
            \*
            \* This is required for the invariant check, since in 3 ticks, given only
            \* one type of failover is allowed (due to constraint in config tick type), 
            \* i.e. GRACEFUL or UNGRACEFUL, there is a scenario
            \* where a write region heartbeats but not applies topology, then a GRACEFUL failover
            \* is triggered but never completes and timesout. The write region is declared as dead
            \* by self terminating i.e. NotHeartbeating state. Now, the write region is not available to take
            \* incoming client writes, and also an UNGRACEFUL failover cannot be initiated since
            \* one failover has already been initiated earlier, thereby failing the invariant check
            \* that write region should be able to take client writes at the end of history.
            \*
            /\  (Cardinality(recentHistoryEntries[index].deadRegions) + 
                Cardinality(recentHistoryEntries[index].aliveRegions)) = Cardinality(Regions)

IsUserPreferredWriteRegionStableInHistory(recentHistoryEntries) ==
    /\  \A index \in 1..Len(recentHistoryEntries):
        /\  ~recentHistoryEntries[index].isPreferredWriteRegionChanged
    /\  ~IsPreferredWriteRegionChangedInCurrentTick

IsEnoughHistory(recentHistoryEntries) ==
    /\  Len(recentHistoryEntries) >= NumberOfHistoryTicksToLookback

IsCurrentWriteRegionAliveInHistoryEntry(lastRecentHistoryEntry) ==
    /\  lastRecentHistoryEntry.currentWriteRegion \in lastRecentHistoryEntry.aliveRegions

IsCurrentWriteRegionTakingClientWrites ==
    /\  RegionCurrentServiceStatus[GlobalCurrentWriteRegion] = ReadWrite

NoFailoverInProgressAtEndOfHistoryWhenRegionsSetIsStable ==
    /\  IF IsEnoughHistory(RegionStateHistory)
        THEN
            LET
                lengthOfFullHistory == Len(RegionStateHistory)
                lastRecentHistoryEntry == RegionStateHistory[lengthOfFullHistory]
                recentHistoryEntries == SubSeq(RegionStateHistory, lengthOfFullHistory - NumberOfHistoryTicksToLookback + 1, lengthOfFullHistory)
            IN
                IF
                    /\  IsEnoughHistory(recentHistoryEntries)
                    /\  IsRegionSetStableInHistory(recentHistoryEntries)
                    /\  IsUserPreferredWriteRegionStableInHistory(recentHistoryEntries)
                THEN
                    /\  ~IsAnyFailoverInProgress(lastRecentHistoryEntry.failoverStatus)
                ELSE
                    TRUE
        ELSE
            TRUE

WritesEnabledAtEndOfHistoryWhenRegionsSetIsStable ==
    /\  IF IsEnoughHistory(RegionStateHistory)
        THEN
            LET
                lengthOfFullHistory == Len(RegionStateHistory)
                lastRecentHistoryEntry == RegionStateHistory[lengthOfFullHistory]
                recentHistoryEntries == SubSeq(RegionStateHistory, lengthOfFullHistory - NumberOfHistoryTicksToLookback + 1, lengthOfFullHistory)
            IN
                IF
                    /\  IsEnoughHistory(recentHistoryEntries)
                    /\  IsRegionSetStableInHistory(recentHistoryEntries)
                    /\  IsUserPreferredWriteRegionStableInHistory(recentHistoryEntries)
                THEN
                    /\  IsCurrentWriteRegionAliveInHistoryEntry(lastRecentHistoryEntry)
                    \*  If there is a failover in the current tick (tick after the lastRecentHistoryEntry), 
                    \*  then the write region may not be able to take client writes.
                    /\  ~IsAnyFailoverInProgress(GlobalFailoverStatus) => IsCurrentWriteRegionTakingClientWrites
                ELSE
                    TRUE
        ELSE
            TRUE

RegionsAbleToApplyTopologyIfHeartbeatingWithGlobalState ==
    LET heartbeatingNotAppliedRegions == {
            region \in Regions:
                /\  HasRegionHeartbeatedWithGlobalStateAtClockTick(region, CurrentClockTick)
                /\  ~HasRegionAppliedComputedTopologyAtClockTick(region, CurrentClockTick)
        }
    IN
        \A region \in heartbeatingNotAppliedRegions:
            ENABLED(ApplyComputedTopologyOnRegion(region))

Inv ==
    /\  TypeOK
    /\  NoFailoverInProgressAtEndOfHistoryWhenRegionsSetIsStable
    /\  WritesEnabledAtEndOfHistoryWhenRegionsSetIsStable
    /\  RegionsAbleToApplyTopologyIfHeartbeatingWithGlobalState

ReadProperty ==
    [][
        LastReadData'.Data >= LastReadData.Data
    ]_<< LastReadData >>
=============================================================================