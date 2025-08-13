-- Start: taken from Level 2
have h_antitone (H K : Set (Set U)) (h1 : H ⊆ K) : ⋂₀ K ⊆ ⋂₀ H
. intro x hx
  intro A hAH
  have hAK := h1 hAH
  rewrite [mem_sInter] at hx
  exact hx A hAK
-- End: taken from Level 2 end

-- Start: lemmas
have h_in_union_left {V} (A B : Set V) : A ⊆ A ∪ B
· intro a ha
  left
  exact ha
--
have h_in_union_right {V} (A B : Set V) : B ⊆ A ∪ B
· rewrite [union_comm]
  exact h_in_union_left B A
--
have h_in_inter {V} (A B C: Set V) (h1 : A ⊆ B) (h2 : A ⊆ C) : A ⊆ B ∩ C
· intro x hx
  exact ⟨h1 hx, h2 hx⟩
-- End: lemmas

apply Subset.antisymm
· have hF : F ⊆ F ∪ G := h_in_union_left F G
  have hG : G ⊆ F ∪ G := h_in_union_right F G
  apply h_antitone at hF
  apply h_antitone at hG
  exact h_in_inter _ _ _ hF hG
· intro x ⟨hxF, hxG⟩
  intro A hA
  rcases hA with hAF | hAG
  · exact hxF A hAF
  · exact hxG A hAG
