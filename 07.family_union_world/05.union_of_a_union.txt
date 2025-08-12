have in_union_left {V} (A B : Set V) : A ⊆ A ∪ B
· intro a ha
  left
  exact ha

have in_union_right {V} (A B : Set V) : B ⊆ A ∪ B
· rewrite [union_comm]
  exact in_union_left B A

have union_in {V} (A B C : Set V) (h1 : A ⊆ C) (h2 : B ⊆ C) : A ∪ B ⊆ C
· intro x hxAB
  rcases hxAB with hxA | hxB
  · exact h1 hxA
  · exact h2 hxB

have fam_union_isotone {V} (H K : Set (Set V)) (h : H ⊆ K) : ⋃₀ H ⊆ ⋃₀ K
· intro x hxH
  obtain ⟨A, ⟨hAH, hxA⟩⟩ := hxH
  have hAK := h hAH
  exact Exists.intro A ⟨hAK, hxA⟩

apply Subset.antisymm
· intro x hxFG
  obtain ⟨A, ⟨hAFG, hxA⟩⟩ := hxFG
  rcases hAFG with hAF | hAG
  · left
    exact Exists.intro A ⟨hAF, hxA⟩
  · right
    exact Exists.intro A ⟨hAG, hxA⟩
· have hF := in_union_left F G
  have hG := in_union_right F G
  apply fam_union_isotone at hF
  apply fam_union_isotone at hG
  exact union_in _ _ _ hF hG
