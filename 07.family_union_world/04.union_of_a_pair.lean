apply Subset.antisymm
· intro x hxAB
  rcases hxAB with hxA | hxB
  · have hA : A ∈ {A, B} := by left; rfl
    exact Exists.intro A ⟨hA, hxA⟩
  · have hB : B ∈ {A, B} := by right; rfl
    exact Exists.intro B ⟨hB, hxB⟩

· intro x hxAB
  obtain ⟨s, ⟨hxAB, hxs⟩⟩ := hxAB
  rcases hxAB with hxA | hxB
  · left
    rewrite [← hxA]
    exact hxs
  · right
    rewrite [← hxB]
    exact hxs
