apply Iff.intro
· exact compl_subset_compl_of_subset
· intro h
  apply compl_subset_compl_of_subset at h
  rewrite [compl_compl A, compl_compl B] at h
  exact h
