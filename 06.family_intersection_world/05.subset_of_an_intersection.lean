constructor
· intro hA
  intro B hB
  intro a ha
  exact hA ha B hB
· intro h_all
  intro a ha
  intro B hB
  exact h_all B hB ha
