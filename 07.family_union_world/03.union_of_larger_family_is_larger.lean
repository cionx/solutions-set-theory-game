intro x hxF
obtain ⟨A, ⟨hAF, hxA⟩⟩ := hxF
have hAG : A ∈ G := h1 hAF
exact Exists.intro A ⟨hAG, hxA⟩
