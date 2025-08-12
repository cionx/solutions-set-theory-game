-- There are shorter solutions to this level, but I think that this is a more conceptual one:
-- We know that (–)ᶜ is involutive and antitone. It is therefore a self-duality of posets.
-- This entails that (–)ᶜ interchanges suprema and infima.
-- But these are precise unions and intersections.

-- This has been proven in the Intersection World but wasn’t remembered.
have h_inter_in (C D : Set U) : C ∩ D ⊆ C
· intro x ⟨hc, hd⟩
  exact hc

have h_in_inter (A C D : Set U) (h1 : A ⊆ C) (h2 : A ⊆ D) : A ⊆ C ∩ D
· intro x ha
  constructor
  · exact h1 ha
  · exact h2 ha

-- This has been proven in the Union World but wasn’t remembered.
have h_in_union (C D : Set U) : C ⊆ C ∪ D
· intro x hc
  exact Or.inl hc

have h_union_in (C D F : Set U) (h1 : C ⊆ F) (h2 : D ⊆ F) : C ∪ D ⊆ F
· intro x hcd
  rcases hcd with hc | hd
  · exact h1 hc
  · exact h2 hd

apply Subset.antisymm
· have ha : A ⊆ A ∪ B := h_in_union A B
  have hb : B ⊆ A ∪ B
  · rewrite [union_comm]
    exact h_in_union B A
  apply compl_subset_compl_of_subset at ha
  apply compl_subset_compl_of_subset at hb
  exact h_in_inter (A ∪ B)ᶜ Aᶜ Bᶜ ha hb

· -- The dual to the already proven implication is as follows:
  have h_dual (C D : Set U) : Cᶜ ∪ Dᶜ ⊆ (C ∩ D)ᶜ
  · have hc : C ∩ D ⊆ C := h_inter_in C D
    have hd : C ∩ D ⊆ D
    · rewrite [inter_comm]
      exact h_inter_in D C
    apply compl_subset_compl_of_subset at hc
    apply compl_subset_compl_of_subset at hd
    exact h_union_in Cᶜ Dᶜ (C ∩ D)ᶜ hc hd

  have h : Aᶜᶜ ∪ Bᶜᶜ ⊆ (Aᶜ ∩ Bᶜ)ᶜ := h_dual Aᶜ Bᶜ
  rewrite [compl_compl A] at h
  rewrite [compl_compl B] at h
  apply compl_subset_compl_of_subset at h
  rewrite [compl_compl] at h
  exact h
