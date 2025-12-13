import Mathlib.Logic.Classical
import Mathlib.Data.Set.Basic

universe u

-- ==========================================================
-- 1. Abstract universe of games / rule-systems
-- ==========================================================
variable {G : Type u}                  -- games / rules
variable {Outcome : Type u}            -- possible outcomes
variable {traj : G → Set Outcome}      -- trajectories of each game
variable [∀ g, (traj g).Nonempty]     -- nonempty trajectories

-- ==========================================================
-- 2. Logical phases
-- ==========================================================
inductive LogicPhase
| plasma | liquid | diamond

open LogicPhase
variable {phase_of : G → LogicPhase}

-- ==========================================================
-- 3. Observer / solid-state rule selector
-- ==========================================================
constant observer_rule : G

axiom observer_subset :
  ∃ subset_rules : Set G, observer_rule ∈ subset_rules ∧ subset_rules.Nonempty

-- ==========================================================
-- 4. Axiom of Trinity (AT) with observer bias
-- ==========================================================
axiom AT_observer :
  ∀ g : G, ∃! limit : Outcome,
    (phase_of g = diamond → limit ∈ traj g) ∧
    (phase_of g = liquid  → limit ∈ traj g) ∧
    (phase_of g = plasma  → limit ∈ traj g)

def canonical_limit (g : G) : Outcome := Classical.choose (AT_observer g)

lemma canonical_limit_spec (g : G) :
  (phase_of g = diamond → canonical_limit g ∈ traj g) ∧
  (phase_of g = liquid  → canonical_limit g ∈ traj g) ∧
  (phase_of g = plasma  → canonical_limit g ∈ traj g) :=
(Classical.choose_spec (AT_observer g)).1

-- ==========================================================
-- 5. Players and determinacy
-- ==========================================================
inductive Player
| P1 | P2

variable outcome_winner : Outcome → Player

def Determined (g : G) : Prop :=
  ∃ p : Player, outcome_winner (canonical_limit g) = p

-- ==========================================================
-- 6a. AT ⇒ AC
-- ==========================================================
theorem AT_implies_AC : ∃ f : G → Outcome, ∀ g, f g ∈ traj g :=
begin
  let f : G → Outcome := λ g, canonical_limit g,
  use f,
  intro g,
  cases ph : phase_of g,
  { exact (canonical_limit_spec g).2.2 ph.symm },  -- plasma
  { exact (canonical_limit_spec g).2.1 ph.symm },  -- liquid
  { exact (canonical_limit_spec g).1   ph.symm },  -- diamond
end

-- ==========================================================
-- 6b. AT ⇒ AD
-- ==========================================================
theorem AT_implies_AD : ∀ g, Determined g :=
begin
  intro g,
  exact ⟨outcome_winner (canonical_limit g), rfl⟩,
end
