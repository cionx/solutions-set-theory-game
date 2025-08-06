ext x
constructor

-- (A ∩ B) ∩ C → A ∩ (B ∩ C)
intro habc
have ha : x ∈ A := habc.left.left
have hb : x ∈ B := habc.left.right
have hc : x ∈ C := habc.right
exact And.intro ha (And.intro hb hc)

-- A ∩ (B ∩ C) → (A ∩ B) ∩ C
intro habc
have ha : x ∈ A := habc.left
have hb : x ∈ B := habc.right.left
have hc : x ∈ C := habc.right.right
exact And.intro (And.intro ha hb) hc
