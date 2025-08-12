intro x hxG
by_cases hxA : x ∈ A
· exact Or.inl hxA
· right
  intro s hsF
  have hAsG : A ∪ s ∈ G := h1 s hsF
  have hxAs : x ∈ A ∪ s := hxG (A ∪ s) hAsG
  rcases hxAs with hxA2 | hxs
  · by_contra hxs  -- We don’t have ex falso.
    exact hxA hxA2
  · exact hxs
