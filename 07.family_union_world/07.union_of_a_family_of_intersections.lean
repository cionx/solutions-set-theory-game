apply Subset.antisymm
· intro x ⟨hxA, hxF⟩
  obtain ⟨u, ⟨huF, hxu⟩⟩ := hxF
  rewrite [mem_sUnion]
  apply Exists.intro (A ∩ u)
  constructor
  · rewrite [mem_setOf]
    apply Exists.intro u
    constructor
    · exact huF
    · rfl
  · exact ⟨hxA, hxu⟩
· intro x hx
  obtain ⟨s, ⟨hs, hxs⟩⟩ := hx
  obtain ⟨u, ⟨huF, hsAu⟩⟩ := hs
  rewrite [hsAu] at hxs
  constructor
  · exact hxs.left
  · apply Exists.intro u
    exact ⟨huF, hxs.right⟩
