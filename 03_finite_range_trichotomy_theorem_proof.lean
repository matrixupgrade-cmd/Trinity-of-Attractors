/-
  toy_phase_trichotomy.lean
  Lightning-minimal toy: discrete complexity, iterate, trichotomy:
    unbounded ∨ (cycle ∨ fixed-point)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open List Nat

/- Minimal state: single natural measuring complexity -/
structure State where
  c : ℕ
deriving Repr, BEq

namespace Toy

variable (evolve : State → State)

/-- iterate evolve n times from s -/
def iterate (n : ℕ) (s : State) : State :=
  (range n).foldl (init := s) fun acc _ => evolve acc

/-- unbounded: for every bound B there is a time with complexity > B -/
def unbounded : Prop := ∀ B : ℕ, ∃ n, (iterate evolve n ⟨0⟩).c > B

/-- bounded by B -/
def bounded (B : ℕ) : Prop := ∀ n, (iterate evolve n ⟨0⟩).c ≤ B

/-- there is a cycle: two distinct times give same full state -/
def has_cycle : Prop := ∃ p q, p < q ∧ iterate evolve p ⟨0⟩ = iterate evolve q ⟨0⟩

/-- frozen: a fixed point is reached -/
def frozen : Prop := ∃ n, evolve (iterate evolve n ⟨0⟩) = iterate evolve n ⟨0⟩

/-- trichotomy: unbounded OR (cycle OR fixed-point) -/
theorem phase_trichotomy :
  unbounded evolve ∨ (has_cycle evolve ∨ frozen evolve) := by
  by_cases h_unb : unbounded evolve
  · left; exact h_unb
  -- not unbounded: there exists B with all complexities ≤ B
  push_neg at h_unb
  rcases h_unb with ⟨B, h_bounded⟩
  right
  /-
    Consider N = B + 2 iterates. Their complexities lie in 0..B (B+1 values),
    so by pigeonhole two indices i<j must have same complexity. Since State = ⟨c⟩,
    equal complexity ⇒ equal state. If j = i+1 we get a fixed point, else a cycle.
  -/
  let N := B + 2
  -- build the list of the first N iterates
  let seq := (range N).map fun k => iterate evolve k ⟨0⟩
  have h_len : seq.length = N := by
    simp [seq]; simp [List.length_map]; simp [List.length_range]
  -- map to complexities
  let cseq := seq.map fun s => s.c
  have cseq_len : cseq.length = N := by simp [cseq]; simp [List.length_map]; simp [h_len]
  -- each complexity ≤ B
  have bound_vals : ∀ k, k < N → cseq.get! k ≤ B := by
    intro k hk
    have : (iterate evolve k ⟨0⟩).c ≤ B := by
      have : k < N := hk
      have : k < B + 2 := hk
      -- h_bounded applies to all n
      exact h_bounded k
    simp [cseq]; simp [seq]; simp
    exact this
  -- Pigeonhole: there must be i < j with equal complexity
  have exists_dup : ∃ i j, i < j ∧ cseq.get! i = cseq.get! j := by
    -- assume no duplicates among indices 0..N-1, derive contradiction
    by_contra h
    push_neg at h
    -- build injective map Fin N → Fin (B+1) sending k ↦ (iterate k).c : Fin (B+1)
    have Npos : 0 < N := by simp [N]; linarith
    let f (k : Fin N) : Fin (B + 1) :=
      ⟨cseq.get! k.val, by
        have hk : k.val < N := k.is_lt
        have := bound_vals k.val hk
        apply Nat.lt_succ_of_le
        exact this⟩
    have fin_inj : Function.Injective f := by
      intro a b hab
      -- equality of f a and f b gives equality of values of cseq.get!
      have : cseq.get! a.val = cseq.get! b.val := by
        congr; exact congrArg Subtype.val hab
      -- but by h (no duplicates), equal complexities at indices imply equal indices
      have a_ltN : a.val < N := a.is_lt
      have b_ltN : b.val < N := b.is_lt
      specialize h a.val b.val a_ltN b_ltN
      -- h states cseq.get! a ≠ cseq.get! b when a.val ≠ b.val; contrapositive gives a.val = b.val
      by_cases a_eq_b : a.val = b.val
      · exact a_eq_b
      · -- since a.val ≠ b.val, h yields inequality contradiction with `this`
        have : cseq.get! a.val ≠ cseq.get! b.val := h
        contradiction
    -- injective map Fin N → Fin (B+1) implies card Fin N ≤ card Fin (B+1)
    have : (Fin.card (Fin N)) ≤ (Fin.card (Fin (B + 1))) := by
      -- use cardinality monotonicity of injective maps on finite types
      apply Fintype.card_le_of_injective f fin_inj
    -- but Fin.card (Fin n) = n
    have : N ≤ (B + 1) := by
      simpa using this
    -- contradiction since N = B+2
    simp [N] at this
    linarith
  -- obtain indices i < j with equal complexity
  rcases exists_dup with ⟨i, j, hij, heq⟩
  -- equal complexities imply equal states because State is just ⟨c⟩
  have state_eq : iterate evolve i ⟨0⟩ = iterate evolve j ⟨0⟩ := by
    cases iterate evolve i ⟨0⟩; cases iterate evolve j ⟨0⟩; simp at heq; congr
  -- if adjacent, fixed point
  by_cases adj : j = i + 1
  · subst adj
    -- iterate (i+1) = evolve (iterate i), but equals iterate i by state_eq, so fixed
    have : iterate evolve (i + 1) ⟨0⟩ = iterate evolve i ⟨0⟩ := by
      -- iterate (i+1) = evolve (iterate i)
      simp [iterate]
      -- state_eq gives iterate (i+1) = iterate j = iterate i
      simpa using state_eq
    have fixed : evolve (iterate evolve i ⟨0⟩) = iterate evolve i ⟨0⟩ := by
      -- left side = iterate (i+1), so equality above gives fixed
      simp [iterate] at this
      exact this
    right; left; use i; exact fixed
  -- otherwise a genuine cycle
  right; right; use i, j; constructor; assumption

end Toy
