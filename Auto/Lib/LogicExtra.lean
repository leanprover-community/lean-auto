namespace Auto

theorem And.assoc : a ∧ b ∧ c ↔ (a ∧ b) ∧ c :=
  Iff.intro (fun ⟨ha, ⟨hb, hc⟩⟩ => ⟨⟨ha, hb⟩, hc⟩) (fun ⟨⟨ha, hb⟩, hc⟩ => ⟨ha, ⟨hb, hc⟩⟩)

theorem Or.assoc : a ∨ b ∨ c ↔ (a ∨ b) ∨ c :=
  Iff.intro
    (fun habc => habc.elim (fun ha => .inl (.inl ha)) (fun hbc =>
      hbc.elim (fun hb => .inl (.inr hb)) (fun hc => .inr hc)))
    (fun habc => habc.elim (fun hab => hab.elim (fun ha => .inl ha) (fun hb => .inr (.inl hb)))
      (fun hc => .inr (.inr hc)))

end Auto