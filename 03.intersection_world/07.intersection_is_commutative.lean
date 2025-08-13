ext x
constructor
· intro ⟨⟨ha, hb⟩, hc⟩
  exact ⟨ha, ⟨hb, hc⟩⟩
· intro ⟨ha, ⟨hb, hc⟩⟩
  exact ⟨⟨ha, hb⟩, hc⟩
