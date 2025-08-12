constructor
· intro hFA
  intro s hsF
  intro x hxs
  apply hFA
  exact Exists.intro s ⟨hsF, hxs⟩
· intro hFA
  intro x hxF
  obtain ⟨s, ⟨hsF, hxs⟩⟩ := hxF
  exact hFA s hsF hxs
