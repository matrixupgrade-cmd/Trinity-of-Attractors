import Mathlib.Data.Set.Basic
import Mathlib.Logic.Basic

universe u

variable {R : Type u}                  -- rule systems

inductive Phase
  | solid
  | liquid
  | plasma
  deriving DecidableEq

open Phase

variable {phase_of_1 phase_of_2 : R → Phase}  -- two observers' phase assignments
variable {shared : Set R}                     -- rules visible to both

-- Trajectory: possible future phases a rule can take
variable {traj : R → Set Phase}
variable [∀ r, Nonempty (traj r)]             -- every rule can evolve somewhere

-- Simplified Axiom of Trinity: each rule has a unique canonical phase in its trajectory
axiom AT : ∀ r, ∃! p : Phase, p ∈ traj r

noncomputable def canonical (r : R) : Phase := Classical.choose (AT r)

lemma canonical_in_traj (r : R) : canonical r ∈ traj r :=
  (Classical.choose_spec (AT r)).1

-- ==========================================================
-- Best-guess coupling operator: emergent phase from two observers
-- ==========================================================
def coupling_phase (r : R) : Phase :=
  if r ∈ shared then
    match phase_of_1 r, phase_of_2 r with
    | solid,   solid   => solid
    | liquid,  _       => liquid
    | _,       liquid  => liquid
    | plasma,  _       => plasma
    | _,       plasma  => plasma
    | _,       _       => liquid  -- any other conflict → bounded mutability
  else
    phase_of_1 r  -- outside shared: observer 1's view dominates (arbitrary choice)

-- ==========================================================
-- Key theorem: As long as the observers disagree somewhere, solidity fails
-- ==========================================================
theorem coupling_prevents_global_solidity
  (h_shared : shared.Nonempty)
  (h_disagree : ∃ r ∈ shared, phase_of_1 r ≠ phase_of_2 r) :
  ∃ r, coupling_phase r ≠ solid :=
begin
  obtain ⟨r, hr_shared, h_ne⟩ := h_disagree,
  use r,
  simp [coupling_phase, hr_shared],
  cases h1 : phase_of_1 r <;> cases h2 : phase_of_2 r <;>
    simp [h1, h2] at h_ne ⊢,
  all_goals { contradiction <|> decide },
end

-- ==========================================================
-- Even stronger: Perfect solidity in coupling requires perfect agreement
-- ==========================================================
theorem solidity_only_if_perfect_agreement
  (h_shared : shared.Nonempty) :
  (∀ r, coupling_phase r = solid) →
  ∀ r ∈ shared, phase_of_1 r = solid ∧ phase_of_2 r = solid :=
begin
  intros h_all_solid r hr_shared,
  have := h_all_solid r,
  simp [coupling_phase, hr_shared] at this,
  split <;>
    cases p1 : phase_of_1 r <;> cases p2 : phase_of_2 r <;>
    simp [p1, p2] at this <;>
    assumption
end

-- ==========================================================
-- Interpretation
-- ==========================================================
/-
The coupling of two observers cannot achieve global solidity
unless they perfectly agree on "solid" for every shared rule.

Any disagreement — even a single rule seen as liquid or plasma by one observer —
injects mutability into the combined system.

This is the mathematical echo of:
  "Perfect symmetry → possible stasis"
  "Any asymmetry → inevitable metamorphosis"

The tension spiders aren't in the code yet — but they live in that disagreement point.
Future versions: make coupling_phase evolve over time, with traj and canonical driving spider-like probes.
-/
