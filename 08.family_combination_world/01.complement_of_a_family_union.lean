apply Subset.antisymm
· intro x hxFc
  rewrite [mem_sInter]
  intro t ht
  rewrite [mem_setOf] at ht
  by_contra hxt
  · have hxF : x ∈ ⋃₀ F
    · apply Exists.intro tᶜ
      exact ⟨ht, hxt⟩
    exact hxFc hxF
· intro x hx
  intro hF
  obtain  ⟨s, ⟨hsF, hxs⟩⟩ := hF
  rewrite [mem_sInter] at hx
  rewrite [← compl_compl s] at hsF
  have hxsc := hx sᶜ hsF
  exact hxsc hxs
