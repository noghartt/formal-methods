// How to run:
// quint verify ./spec.qnt --temporal liveness,guarantees --invariant Inv

module TwoPhaseCommit {
  import customSpells.* from "../quint_spells/customSpells"
  import basicSpells.* from "../quint_spells/basicSpells"
  import commonSpells.* from "../quint_spells/commonSpells"

  type NodeID = int
  type TNodes = Set[NodeID]

  type Message =
    | Prepare
    | PrepareAck
    | Commit
    | CommitAck
    | Abort

  type State =
    | Idle 
    | Prepared 
    | Committing
    | Aborted 
    | Committed

  type MessageState = { from: int, to: int, msg: Message }

  val Nodes = 1.to(3)
  val TransactionManager = 1

  var nodeStates: NodeID -> State
  var msgs: Set[MessageState]

  def countMessages(m: Message): int = {
    size(msgs.filter(__m => __m.msg == m))
  }

  action init = all {
    msgs' = Set(),
    nodeStates' = Nodes.mapBy(_ => Idle)
  }

  action coordinatorSendPrepare = {
    val recipients = Nodes.filter(n => n != TransactionManager)
    all {
      nodeStates.get(TransactionManager) == Idle,
      msgs' = msgs.union(recipients.map(n => { from: TransactionManager, to: n, msg: Prepare })),
      nodeStates' = nodeStates.put(TransactionManager, Prepared),
    }
  }

  action coordinatorSendCommit = {
    val recipients = Nodes.filter(n => n != TransactionManager)
    val hasAbortMessage = msgs.exists(m => m.msg == Abort)
    all {
      nodeStates.get(TransactionManager) == Prepared,
      if (hasAbortMessage) {
        all {
          msgs' = msgs.union(recipients.map(n => { from: TransactionManager, to: n, msg: Abort })),
          nodeStates' = nodeStates.put(TransactionManager, Aborted)
        }     
      } else {
        all {
          countMessages(PrepareAck) == size(Nodes) - 1,
          msgs' = msgs.union(recipients.map(n => { from: TransactionManager, to: n, msg: Commit })),
          nodeStates' = nodeStates.put(TransactionManager, Committing)
        }
      }
    }
  }

  action coordinatorDecideOnCommit = all {
    and {
      nodeStates.get(TransactionManager) == Committing,
      countMessages(CommitAck) == size(Nodes) - 1,
    },
    nodeStates' = nodeStates.put(TransactionManager, Committed),
    msgs' = msgs,
  }

  action coordinatorDecideOnAbort =
    val transactionManagerState = nodeStates.get(TransactionManager)
    val recipients = Nodes.filter(n => n != TransactionManager)
    all {
      or {
        transactionManagerState == Prepared,
        transactionManagerState == Committing,
      },
      mapToSet(nodeStates).exists(n => n._2 == Aborted),
      nodeStates' = nodeStates.put(TransactionManager, Aborted),
      msgs' = msgs.union(recipients.map(n => { from: TransactionManager, to: n, msg: Abort })),
    } 

  action participantDecideOnAbort(n) =
    val hasRollbackMsg = msgs.contains({ from: TransactionManager, to: n, msg: Abort })
    val nodeState = nodeStates.get(n)
    all {
      hasRollbackMsg,
      nodeState != Aborted,
      nodeStates' = nodeStates.put(n, Aborted),
      msgs' = msgs.union(Set({ from: n, to: TransactionManager, msg: Abort })),
    }

  action participantHandlePrepare(n) = all {
    and {
      nodeStates.get(n) == Idle,
      msgs.contains({ from: TransactionManager, to: n, msg: Prepare }),
    },
    any {
      all {
        nodeStates' = nodeStates.put(n, Prepared),
        msgs' = msgs
          .union(Set({ from: n, to: TransactionManager, msg: PrepareAck })),
      },
      all {
        nodeStates' = nodeStates.put(n, Aborted),
        msgs' = msgs
          .union(Set({ from: n, to: TransactionManager, msg: Abort }))
      }
    }
  }

  action participantHandleCommit(n) = all {
    and {
      nodeStates.get(n) == Prepared,
      msgs.contains({ from: TransactionManager, to: n, msg: Commit }),
    },
    all {
      nodeStates' = nodeStates.put(n, Committed),
      msgs' = msgs.union(Set({ from: n, to: TransactionManager, msg: CommitAck }))
    },
  }

  action stuttering = all {
    Nodes.forall(n => Set(Aborted, Committed).contains(nodeStates.get(n))),
    msgs' = msgs,
    nodeStates' = nodeStates,
  }

  action step = any {
    stuttering,
    any {
      coordinatorSendPrepare,
      coordinatorSendCommit,
      coordinatorDecideOnCommit,
      coordinatorDecideOnAbort,
    },
    nondet node = Nodes.filter(n => n != TransactionManager).oneOf()
    any {
      participantDecideOnAbort(node),
      participantHandlePrepare(node),
      participantHandleCommit(node),
    }
  }

  // Invariants
  val consistency = tuples(Nodes, Nodes).forall(
    ((n1, n2)) => not(nodeStates.get(n1) == Committed and nodeStates.get(n2) == Aborted)
  )
    
  val Inv = consistency

  // TEMPORAL PROPERTIES
  val terminationDetected = 
    Nodes.forall(n => Set(Aborted, Committed).contains(nodeStates.get(n)))
  
  temporal guarantees = and {
    always(mapToSet(nodeStates).exists(n => n._2 == Aborted))
      implies always(size(mapToSet(nodeStates).filter(n => n._2 == Aborted)) > 0)
  }

  temporal liveness =
    always(Nodes.forall(n => Set(Aborted, Committed).contains(nodeStates.get(n))))
      implies eventually(terminationDetected)
}
