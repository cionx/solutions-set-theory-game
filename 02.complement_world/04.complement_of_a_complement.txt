apply Subset.antisymm
· intro x hx
  rewrite [mem_compl_iff, mem_compl_iff] at hx
  push_neg at hx
  exact hx
· intro x hx1
  rewrite [mem_compl_iff]
  intro hx2
  rewrite [mem_compl_iff] at hx2
  exact hx2 hx1
