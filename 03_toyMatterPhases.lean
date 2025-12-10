theorem phase_trichotomy (evolve : State → State) :
  Toy.unbounded evolve ∨ (Toy.has_cycle evolve ∨ Toy.frozen evolve) :=
by
  by_cases h : Toy.unbounded evolve
  · left; exact h
  · push_neg at h
    rcases h with ⟨B, hB⟩
    let states := (range (B+2)).map (λ k => iterate evolve k ⟨0⟩)
    have h_len : states.length = B+2 := by simp [Nat.add_comm]
    have h_bound : ∀ s ∈ states, s.c ≤ B := by
      simp [mem_map, mem_range]; rintro s ⟨k, hk, rfl⟩; apply hB
    have := pigeonhole_of_length_gt_card states (by linarith) fun s hs =>
      Finset.mem_Icc.mpr ⟨c_nonneg s, h_bound s hs⟩
    rcases this with ⟨s, ⟨i, hi⟩, ⟨j, hj⟩, hij, hseq⟩
    have heq : iterate evolve i ⟨0⟩ = iterate evolve j ⟨0⟩ := by
      cases iterate evolve i ⟨0⟩; cases iterate evolve j ⟨0⟩
      congr
    right
    by_cases h_adj : j = i + 1
    · right; use i
      rw [iterate_succ, h_adj] at hseq
      exact hseq
    · left; use i, j
      constructor
      · exact hij
      · exact heq
