intro x ⟨hxF, hxGc⟩
obtain ⟨s, ⟨hsF, hxs⟩⟩ := hxF
use s
constructor
· constructor
  · exact hsF
  · intro hsG
    rewrite [mem_compl_iff] at hxGc
    rewrite [mem_sUnion] at hxGc
    push_neg at hxGc
    exact hxGc s hsG hxs
· exact hxs
