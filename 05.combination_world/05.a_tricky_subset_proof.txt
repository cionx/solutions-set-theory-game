intro x ha
have hac : x ∈ A ∪ C := Or.inl ha
have hbc := h1 hac
rcases hbc with hb | hc
· exact hb
· have hac2 : x ∈ A ∩ C := ⟨ha, hc⟩
  have ⟨hb, hc2⟩ : x ∈ B ∩ C := h2 hac2
  exact hb

/- Another proof:
-- A
-- = A ∩ U
-- = A ∩ (C ∪ Cᶜ)
-- = (A ∩ C) ∪ (A ∩ Cᶜ)
-- ⊆ (B ∩ C) ∪ ((A ∪ C) ∩ Cᶜ)
-- ⊆ (B ∩ C) ∪ ((B ∪ C) ∩ Cᶜ)
-- = B ∩ (C ∪ Cᶜ)
-- = B ∩ U
-- = B.
-- But this proof needs a bunch of lemmas.
-/
