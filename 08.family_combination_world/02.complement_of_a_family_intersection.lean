apply Subset.antisymm
· intro x hx
  rewrite [mem_sUnion]
  rewrite [mem_compl_iff] at hx
  rewrite [mem_sInter] at hx
  push_neg at hx
  obtain ⟨t, ht⟩ := hx
  apply Exists.intro tᶜ
  rewrite [mem_setOf]
  rewrite [compl_compl]
  exact ht
· intro x hx
  obtain ⟨s, ⟨hs1, hs2⟩⟩ := hx
  rewrite [mem_setOf] at hs1
  intro hxF
  have hxsc := hxF sᶜ hs1
  exact hxsc hs2
