// -*- mode: Bluespec; -*-

module customSpells {
  pure def setToList(__set: Set[a]): List[a] = {
    __set.fold(List(), ((l, i) => l.append(i)))
  }

  pure def listLength(__list: List[a]): int = {
    length(__list)
  }
}
