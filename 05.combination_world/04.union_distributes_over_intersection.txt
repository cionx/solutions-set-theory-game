have h := inter_distrib_left Aᶜ Bᶜ Cᶜ
rewrite [← compl_inter B C] at h
rewrite [← compl_union A (B ∩ C)] at h
rewrite [← compl_union A B] at h
rewrite [← compl_union A C] at h
rewrite [← compl_inter (A ∪ B) (A ∪ C)] at h
rewrite [← compl_compl (A ∪ B ∩ C)]
rewrite [h]
exact compl_compl ((A ∪ B) ∩ (A ∪ C))
