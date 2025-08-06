intro a ha
have hb : a ∈ B := h1 ha
have hc : a ∈ C := h2 ha
exact And.intro hb hc
