apply Subset.antisymm
· intro x ⟨ha, hbc⟩
  rcases hbc with hb | hc
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hc⟩
· intro x habac
  rcases habac with ⟨ha, hb⟩ | ⟨ha, hc⟩
  · exact ⟨ha, (Or.inl hb)⟩
  · exact ⟨ha, (Or.inr hc)⟩
