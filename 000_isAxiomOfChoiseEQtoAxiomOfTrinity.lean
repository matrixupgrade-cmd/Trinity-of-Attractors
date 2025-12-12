import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Classical

universe u

-- ==========================================================
-- Basic setup
-- ==========================================================
variable {L : Type u}        -- class of all rules/statements
variable {traj : L → Set L}  -- trajectory/evolution set of each rule
variable [∀ l, (traj l).Nonempty]

inductive LogicPhase | immutable | stable | escaping

variable {phase_of : L → LogicPhase}

-- 4th observer rule exists only in solid (immutable) state
constant observer_rule : L

-- ==========================================================
-- Axiom of Trinity (Metamorphosis version with observer)
-- ==========================================================
axiom trinity_metamorphosis :
  ∀ l, ∃! limit : L,
    (phase_of l = LogicPhase.immutable → limit ∈ traj l ∧ l ≠ observer_rule) ∧
    (phase_of l = LogicPhase.stable    → limit ∈ traj l) ∧
    (phase_of l = LogicPhase.escaping  → limit ∈ traj l)

-- ==========================================================
-- AC as solid-state observer picking a subset of rules
-- ==========================================================
axiom AC_solid_observer :
  ∃ subset_rules : Set L, observer_rule ∈ subset_rules ∧ subset_rules.Nonempty

-- ==========================================================
-- Trinity → AC
-- ==========================================================
theorem trinity_metamorphosis_implies_AC :
  ∃ choice : L → L, ∀ l, choice l ∈ traj l :=
begin
  let choice : L → L := λ l, (trinity_metamorphosis l).choose,
  use choice,
  intro l,
  set limit := choice l with h_limit_def,
  have h_spec := (trinity_metamorphosis l).choose_spec.1,
  cases ph : phase_of l,
  { exact h_spec.1 ph.symm.1, },   -- immutable: solid rules, observer rule excluded
  { exact h_spec.2.1 ph.symm.1, }, -- stable: liquid rules
  { exact h_spec.2.2 ph.symm, },   -- escaping: plasma rules
end

-- ==========================================================
-- AC → Trinity (with observer)
-- ==========================================================
theorem AC_implies_trinity_metamorphosis
  (AC : ∃ f : L → L, ∀ l, f l ∈ traj l) :
  ∀ l, ∃! limit : L,
    (phase_of l = LogicPhase.immutable → limit ∈ traj l ∧ l ≠ observer_rule) ∧
    (phase_of l = LogicPhase.stable    → limit ∈ traj l) ∧
    (phase_of l = LogicPhase.escaping  → limit ∈ traj l) :=
begin
  obtain ⟨f, hf⟩ := AC,
  
  -- Observer selects subset of rules for the solid state
  obtain ⟨subset_rules, h_obs_mem, h_nonempty⟩ := AC_solid_observer,

  intro l,
  let limit := f l, -- AC picks one element from traj(l)
  have h_limit_in_traj : limit ∈ traj l := hf l,

  -- ==========================================================
  -- Uniqueness: holds for solid (immutable) and liquid (stable)
  -- Plasma/escaping may have multiple possibilities; AC picks one
  -- Observer sees only subset_rules, which is non-empty, ensuring AC has something to pick
  -- ==========================================================
  sorry, -- placeholder for uniqueness reasoning within observer subset
end

-- ==========================================================
-- Full equivalence
-- ==========================================================
theorem trinity_metamorphosis_iff_AC :
  (∃ choice : L → L, ∀ l, choice l ∈ traj l) ↔
  (∀ l, ∃! limit : L,
    (phase_of l = LogicPhase.immutable → limit ∈ traj l ∧ l ≠ observer_rule) ∧
    (phase_of l = LogicPhase.stable    → limit ∈ traj l) ∧
    (phase_of l = LogicPhase.escaping  → limit ∈ traj l)) :=
begin
  split,
  { exact trinity_metamorphosis_implies_AC, },
  { intro h_trinity,
    let choice : L → L := λ l, (h_trinity l).choose,
    use choice,
    intro l,
    have h_spec := (h_trinity l).choose_spec.1,
    cases ph : phase_of l,
    { exact h_spec.1 ph.symm.1, },   -- solid
    { exact h_spec.2.1 ph.symm.1, }, -- liquid
    { exact h_spec.2.2 ph.symm, },   -- plasma
  },
end
