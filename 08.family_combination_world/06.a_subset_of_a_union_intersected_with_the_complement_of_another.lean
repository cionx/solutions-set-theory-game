intro x ⟨hxF, hxG⟩
obtain ⟨s, ⟨hsF : s ∈ F, hxs : x ∈ s⟩⟩ := hxF
have hsG : s ∈ G
· by_contra hsnG
  have hsFGc : s ∈ F ∩ Gᶜ := ⟨hsF, hsnG⟩
  have hxFGc : x ∈ ⋃₀ (F ∩ Gᶜ)
  · use s
  apply h1 at hxFGc
  exact hxFGc.right hxG

have hsFG : s ∈ F ∩ G := ⟨hsF, hsG⟩
use s
