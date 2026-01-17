module TwoPhaseCommit {
  type Msg = { from: int, to: int, value: int }

  var nodes: Set[int]
  var coordinator: int
  var storage: int -> List[int]
  var msgs: List[Msg]

  // TODO: I do believe, I should add the ability to handle scenarios with more nodes.
  //       See a way to generate different traces with different amount of nodes.
  action init = all {
      nodes' = 1.to(3),
      coordinator' = 1,
      storage' = 1.to(3).fold(Map(), (m, n) => m.put(n, List())),
      msgs' = List(),
    }

  action proposeVoting(f, t, v) = {
    nondet value = 1.to(100).oneOf()
    all {
      nodes' = nodes,
      msgs'  = msgs.concat(List({ from: f, to: t, value: value })),
      coordinator' = coordinator,
      storage' = storage
    }
  }

  action step = {
    nondet node = nodes.filter(n => n != coordinator).oneOf()
    all {
      proposeVoting(coordinator, node, 1),
    }
  }
}
