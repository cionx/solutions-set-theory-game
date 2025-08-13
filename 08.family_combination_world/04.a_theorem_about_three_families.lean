intro x ⟨hxF, hxG⟩
obtain ⟨s, ⟨hsF, hxs⟩⟩ := hxF
obtain ⟨u, ⟨huG, hsuH⟩⟩ := h1 s hsF
use s ∩ u
constructor
· exact hsuH
· constructor
  · exact hxs
  · exact hxG u huG
