---------------------------- MODULE TwoPhaseCommit ----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache, Variants

(*
  @type: (() => Set(Int));
*)
Nodes == 1 .. 3

(*
  @type: (() => Int);
*)
TransactionManager == 1

(*
  @type: (() => Abort({ tag: Str }) | Commit({ tag: Str }) | CommitAck({ tag: Str }) | Prepare({ tag: Str }) | PrepareAck({ tag: Str }));
*)
Prepare == Variant("Prepare", [tag |-> "UNIT"])

(*
  @type: (() => Abort({ tag: Str }) | Commit({ tag: Str }) | CommitAck({ tag: Str }) | Prepare({ tag: Str }) | PrepareAck({ tag: Str }));
*)
PrepareAck == Variant("PrepareAck", [tag |-> "UNIT"])

(*
  @type: (() => Abort({ tag: Str }) | Commit({ tag: Str }) | CommitAck({ tag: Str }) | Prepare({ tag: Str }) | PrepareAck({ tag: Str }));
*)
Commit == Variant("Commit", [tag |-> "UNIT"])

(*
  @type: (() => Abort({ tag: Str }) | Commit({ tag: Str }) | CommitAck({ tag: Str }) | Prepare({ tag: Str }) | PrepareAck({ tag: Str }));
*)
CommitAck == Variant("CommitAck", [tag |-> "UNIT"])

(*
  @type: (() => Abort({ tag: Str }) | Commit({ tag: Str }) | CommitAck({ tag: Str }) | Prepare({ tag: Str }) | PrepareAck({ tag: Str }));
*)
Abort == Variant("Abort", [tag |-> "UNIT"])

(*
  @type: (() => Aborted({ tag: Str }) | Committed({ tag: Str }) | Committing({ tag: Str }) | Idle({ tag: Str }) | Prepared({ tag: Str }));
*)
Idle == Variant("Idle", [tag |-> "UNIT"])

(*
  @type: (() => Aborted({ tag: Str }) | Committed({ tag: Str }) | Committing({ tag: Str }) | Idle({ tag: Str }) | Prepared({ tag: Str }));
*)
Prepared == Variant("Prepared", [tag |-> "UNIT"])

(*
  @type: (() => Aborted({ tag: Str }) | Committed({ tag: Str }) | Committing({ tag: Str }) | Idle({ tag: Str }) | Prepared({ tag: Str }));
*)
Committing == Variant("Committing", [tag |-> "UNIT"])

(*
  @type: (() => Aborted({ tag: Str }) | Committed({ tag: Str }) | Committing({ tag: Str }) | Idle({ tag: Str }) | Prepared({ tag: Str }));
*)
Aborted == Variant("Aborted", [tag |-> "UNIT"])

(*
  @type: (() => Aborted({ tag: Str }) | Committed({ tag: Str }) | Committing({ tag: Str }) | Idle({ tag: Str }) | Prepared({ tag: Str }));
*)
Committed == Variant("Committed", [tag |-> "UNIT"])

VARIABLE
  (*
    @type: (Int -> Aborted({ tag: Str }) | Committed({ tag: Str }) | Committing({ tag: Str }) | Idle({ tag: Str }) | Prepared({ tag: Str }));
  *)
  nodeStates

(*
  @type: (((a -> b)) => Set(<<a, b>>));
*)
mapToSet(__map_1749) ==
  LET (*
    @type: ((Set(<<a, b>>), a) => Set(<<a, b>>));
  *)
  __QUINT_LAMBDA0(__acc_1747, __k_1747) ==
    __acc_1747 \union {<<__k_1747, __map_1749[__k_1747]>>}
  IN
  ApaFoldSet(__QUINT_LAMBDA0, {}, (DOMAIN __map_1749))

VARIABLE
  (*
    @type: Set({ from: Int, msg: Abort({ tag: Str }) | Commit({ tag: Str }) | CommitAck({ tag: Str }) | Prepare({ tag: Str }) | PrepareAck({ tag: Str }), to: Int });
  *)
  msgs

(*
  @type: (() => Bool);
*)
consistency ==
  \A quintTupledLambdaParam502_511 \in Nodes \X Nodes:
    LET (*@type: (() => Int); *) n2 == quintTupledLambdaParam502_511[2] IN
    LET (*@type: (() => Int); *) n1 == quintTupledLambdaParam502_511[1] IN
    ~(nodeStates[(n1)] = Committed /\ nodeStates[(n2)] = Aborted)

(*
  @type: (() => Bool);
*)
terminationDetected ==
  \A n_525 \in Nodes: nodeStates[n_525] \in { (Aborted), (Committed) }

(*
  @type: (() => Bool);
*)
guarantees ==
  ([](\E n_536 \in mapToSet(nodeStates): n_536[2] = Aborted)
      => [](Cardinality({ n_547 \in mapToSet(nodeStates): n_547[2] = Aborted })
        > 0))

(*
  @type: (() => Bool);
*)
init == msgs = {} /\ nodeStates = [ id__102 \in Nodes |-> Idle ]

(*
  @type: (() => Bool);
*)
coordinatorSendPrepare ==
  LET (*
    @type: (() => Set(Int));
  *)
  recipients == { n_113 \in Nodes: n_113 /= TransactionManager }
  IN
  nodeStates[(TransactionManager)] = Idle
    /\ msgs'
      := (msgs
        \union {
          [from |-> TransactionManager, to |-> n_131, msg |-> Prepare]:
            n_131 \in recipients
        })
    /\ nodeStates'
      := LET (*
        @type: (() => (Int -> Aborted({ tag: Str }) | Committed({ tag: Str }) | Committing({ tag: Str }) | Idle({ tag: Str }) | Prepared({ tag: Str })));
      *)
      __quint_var0 == nodeStates
      IN
      LET (*@type: (() => Set(Int)); *) __quint_var1 == DOMAIN __quint_var0 IN
      [
        __quint_var2 \in {(TransactionManager)} \union __quint_var1 |->
          IF __quint_var2 = TransactionManager
          THEN Prepared
          ELSE (__quint_var0)[__quint_var2]
      ]

(*
  @type: (() => Bool);
*)
coordinatorDecideOnAbort ==
  LET (*
    @type: (() => Aborted({ tag: Str }) | Committed({ tag: Str }) | Committing({ tag: Str }) | Idle({ tag: Str }) | Prepared({ tag: Str }));
  *)
  transactionManagerState == nodeStates[(TransactionManager)]
  IN
  LET (*
    @type: (() => Set(Int));
  *)
  recipients == { n_258 \in Nodes: n_258 /= TransactionManager }
  IN
  (transactionManagerState = Prepared \/ transactionManagerState = Committing)
    /\ (\E n_276 \in mapToSet(nodeStates): n_276[2] = Aborted)
    /\ nodeStates'
      := LET (*
        @type: (() => (Int -> Aborted({ tag: Str }) | Committed({ tag: Str }) | Committing({ tag: Str }) | Idle({ tag: Str }) | Prepared({ tag: Str })));
      *)
      __quint_var3 == nodeStates
      IN
      LET (*@type: (() => Set(Int)); *) __quint_var4 == DOMAIN __quint_var3 IN
      [
        __quint_var5 \in {(TransactionManager)} \union __quint_var4 |->
          IF __quint_var5 = TransactionManager
          THEN Aborted
          ELSE (__quint_var3)[__quint_var5]
      ]
    /\ msgs'
      := (msgs
        \union {
          [from |-> TransactionManager, to |-> n_294, msg |-> Abort]:
            n_294 \in recipients
        })

(*
  @type: ((Int) => Bool);
*)
participantHandlePrepare(n_401) ==
  (nodeStates[n_401] = Idle
      /\ [from |-> TransactionManager, to |-> n_401, msg |-> Prepare] \in msgs)
    /\ ((nodeStates'
          := LET (*
            @type: (() => (Int -> Aborted({ tag: Str }) | Committed({ tag: Str }) | Committing({ tag: Str }) | Idle({ tag: Str }) | Prepared({ tag: Str })));
          *)
          __quint_var6 == nodeStates
          IN
          LET (*
            @type: (() => Set(Int));
          *)
          __quint_var7 == DOMAIN __quint_var6
          IN
          [
            __quint_var8 \in {n_401} \union __quint_var7 |->
              IF __quint_var8 = n_401
              THEN Prepared
              ELSE (__quint_var6)[__quint_var8]
          ]
        /\ msgs'
          := (msgs
            \union {[from |-> n_401,
              to |-> TransactionManager,
              msg |-> PrepareAck]}))
      \/ (nodeStates'
          := LET (*
            @type: (() => (Int -> Aborted({ tag: Str }) | Committed({ tag: Str }) | Committing({ tag: Str }) | Idle({ tag: Str }) | Prepared({ tag: Str })));
          *)
          __quint_var9 == nodeStates
          IN
          LET (*
            @type: (() => Set(Int));
          *)
          __quint_var10 == DOMAIN __quint_var9
          IN
          [
            __quint_var11 \in {n_401} \union __quint_var10 |->
              IF __quint_var11 = n_401
              THEN Aborted
              ELSE (__quint_var9)[__quint_var11]
          ]
        /\ msgs'
          := (msgs
            \union {[from |-> n_401, to |-> TransactionManager, msg |-> Abort]})))

(*
  @type: ((Int) => Bool);
*)
participantHandleCommit(n_439) ==
  (nodeStates[n_439] = Prepared
      /\ [from |-> TransactionManager, to |-> n_439, msg |-> Commit] \in msgs)
    /\ (nodeStates'
        := LET (*
          @type: (() => (Int -> Aborted({ tag: Str }) | Committed({ tag: Str }) | Committing({ tag: Str }) | Idle({ tag: Str }) | Prepared({ tag: Str })));
        *)
        __quint_var12 == nodeStates
        IN
        LET (*
          @type: (() => Set(Int));
        *)
        __quint_var13 == DOMAIN __quint_var12
        IN
        [
          __quint_var14 \in {n_439} \union __quint_var13 |->
            IF __quint_var14 = n_439
            THEN Committed
            ELSE (__quint_var12)[__quint_var14]
        ]
      /\ msgs'
        := (msgs
          \union {[from |-> n_439, to |-> TransactionManager, msg |-> CommitAck]}))

(*
  @type: (() => Bool);
*)
stuttering ==
  (\A n_450 \in Nodes: nodeStates[n_450] \in { (Aborted), (Committed) })
    /\ msgs' := msgs
    /\ nodeStates' := nodeStates

(*
  @type: ((Abort({ tag: Str }) | Commit({ tag: Str }) | CommitAck({ tag: Str }) | Prepare({ tag: Str }) | PrepareAck({ tag: Str })) => Int);
*)
countMessages(m_94) == Cardinality({ __m_91 \in msgs: __m_91["msg"] = m_94 })

(*
  @type: ((Int) => Bool);
*)
participantDecideOnAbort(n_343) ==
  LET (*
    @type: (() => Bool);
  *)
  hasRollbackMsg ==
    [from |-> TransactionManager, to |-> n_343, msg |-> Abort] \in msgs
  IN
  LET (*
    @type: (() => Aborted({ tag: Str }) | Committed({ tag: Str }) | Committing({ tag: Str }) | Idle({ tag: Str }) | Prepared({ tag: Str }));
  *)
  nodeState == nodeStates[n_343]
  IN
  hasRollbackMsg
    /\ nodeState /= Aborted
    /\ nodeStates'
      := LET (*
        @type: (() => (Int -> Aborted({ tag: Str }) | Committed({ tag: Str }) | Committing({ tag: Str }) | Idle({ tag: Str }) | Prepared({ tag: Str })));
      *)
      __quint_var24 == nodeStates
      IN
      LET (*@type: (() => Set(Int)); *) __quint_var25 == DOMAIN __quint_var24 IN
      [
        __quint_var26 \in {n_343} \union __quint_var25 |->
          IF __quint_var26 = n_343
          THEN Aborted
          ELSE (__quint_var24)[__quint_var26]
      ]
    /\ msgs'
      := (msgs
        \union {[from |-> n_343, to |-> TransactionManager, msg |-> Abort]})

(*
  @type: (() => Bool);
*)
Inv == consistency

(*
  @type: (() => Bool);
*)
liveness ==
  [](\A n_565 \in Nodes: nodeStates[n_565] \in { (Aborted), (Committed) })
    => <>terminationDetected

(*
  @type: (() => Bool);
*)
coordinatorSendCommit ==
  LET (*
    @type: (() => Set(Int));
  *)
  recipients == { n_150 \in Nodes: n_150 /= TransactionManager }
  IN
  LET (*
    @type: (() => Bool);
  *)
  hasAbortMessage == \E m_160 \in msgs: m_160["msg"] = Abort
  IN
  nodeStates[(TransactionManager)] = Prepared
    /\ (IF hasAbortMessage
    THEN msgs'
        := (msgs
          \union {
            [from |-> TransactionManager, to |-> n_179, msg |-> Abort]:
              n_179 \in recipients
          })
      /\ nodeStates'
        := LET (*
          @type: (() => (Int -> Aborted({ tag: Str }) | Committed({ tag: Str }) | Committing({ tag: Str }) | Idle({ tag: Str }) | Prepared({ tag: Str })));
        *)
        __quint_var15 == nodeStates
        IN
        LET (*
          @type: (() => Set(Int));
        *)
        __quint_var16 == DOMAIN __quint_var15
        IN
        [
          __quint_var17 \in {(TransactionManager)} \union __quint_var16 |->
            IF __quint_var17 = TransactionManager
            THEN Aborted
            ELSE (__quint_var15)[__quint_var17]
        ]
    ELSE countMessages((PrepareAck)) = Cardinality((Nodes)) - 1
      /\ msgs'
        := (msgs
          \union {
            [from |-> TransactionManager, to |-> n_208, msg |-> Commit]:
              n_208 \in recipients
          })
      /\ nodeStates'
        := LET (*
          @type: (() => (Int -> Aborted({ tag: Str }) | Committed({ tag: Str }) | Committing({ tag: Str }) | Idle({ tag: Str }) | Prepared({ tag: Str })));
        *)
        __quint_var18 == nodeStates
        IN
        LET (*
          @type: (() => Set(Int));
        *)
        __quint_var19 == DOMAIN __quint_var18
        IN
        [
          __quint_var20 \in {(TransactionManager)} \union __quint_var19 |->
            IF __quint_var20 = TransactionManager
            THEN Committing
            ELSE (__quint_var18)[__quint_var20]
        ])

(*
  @type: (() => Bool);
*)
coordinatorDecideOnCommit ==
  (nodeStates[(TransactionManager)] = Committing
      /\ countMessages((CommitAck)) = Cardinality((Nodes)) - 1)
    /\ nodeStates'
      := LET (*
        @type: (() => (Int -> Aborted({ tag: Str }) | Committed({ tag: Str }) | Committing({ tag: Str }) | Idle({ tag: Str }) | Prepared({ tag: Str })));
      *)
      __quint_var21 == nodeStates
      IN
      LET (*@type: (() => Set(Int)); *) __quint_var22 == DOMAIN __quint_var21 IN
      [
        __quint_var23 \in {(TransactionManager)} \union __quint_var22 |->
          IF __quint_var23 = TransactionManager
          THEN Committed
          ELSE (__quint_var21)[__quint_var23]
      ]
    /\ msgs' := msgs

(*
  @type: (() => Bool);
*)
q_init == init

(*
  @type: (() => Bool);
*)
step ==
  stuttering
    \/ (coordinatorSendPrepare
      \/ coordinatorSendCommit
      \/ coordinatorDecideOnCommit
      \/ coordinatorDecideOnAbort)
    \/ (\E node \in { n_471 \in Nodes: n_471 /= TransactionManager }:
      participantDecideOnAbort(node)
        \/ participantHandlePrepare(node)
        \/ participantHandleCommit(node))

(*
  @type: (() => Bool);
*)
q_step == step

================================================================================
