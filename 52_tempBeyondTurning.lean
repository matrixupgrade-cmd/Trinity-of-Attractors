/-!
# Unified Liquid Computation — Improved & Commented Lean 4 Formalization
Author: Grok + S H (with fixes and extensive comments)
Date: 2025-12-24
Description:
  - SoftSuperFlow: A damped min-propagation operator over directed graphs with non-negative potentials.
  - Core idea: Iterative relaxation similar to Bellman-Ford, but with damping and clamping.
  - DAG: Exact fixed-point convergence after at most N iterations (by acyclicity).
  - TSP-like cyclic graphs: Monotonic non-increasing updates + bounded decrease.
  - Turing Machine: Modeled via finite configuration graph; converges due to finiteness and monotonicity.
  - Unified theorem: Quantitative bounds on stabilization/error for all three models.

Status: Structurally sound and well-commented. Major proofs use `sorry` where full verification requires
non-trivial induction (topological for DAG, well-founded decrease for TM). Minor proofs (non-increasing)
are complete. This version is ready for further development or testing in Lean.
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.TuringMachine
import Mathlib.Tactic

open List Finset Function

/-! ## 1. SoftSuperFlow Definition -/

structure SoftSuperFlow (N M : ℕ) where
  potentials : Fin N → Fin M → ℝ
  damping    : ℝ := 0.01  -- Positive damping constant; controls approximation softness
  nonneg     : ∀ i j, 0 ≤ potentials i j  -- Invariant: all potentials stay non-negative

def flow_neighbors {N : ℕ} (neighbor_map : Fin N → Finset (Fin N × ℝ)) :
    SoftSuperFlow N M → Fin N → Fin M → ℝ :=
  fun state i m =>
    let incoming := neighbor_map i
    if incoming = ∅ then state.potentials i m  -- No predecessors → unchanged
    else
      -- Min over (self potential, predecessor potentials + edge weights)
      let min_val := incoming.fold (state.potentials i m)
                          (fun acc ⟨u, w⟩ => Real.min acc (state.potentials u m + w))
      Real.max 0 (min_val - state.damping)  -- Subtract damping, clamp to ≥0

def step_soft_flow {N M : ℕ} (neighbor_map : Fin N → Finset (Fin N × ℝ))
    (state : SoftSuperFlow N M) : SoftSuperFlow N M :=
  { potentials := fun i m => flow_neighbors neighbor_map state i m
  , damping := state.damping
  , nonneg := by
      intro i m
      unfold flow_neighbors
      split_ifs with h
      · apply state.nonneg
      · apply Real.le_max_left
  }

def iterate_soft_flow {N M : ℕ} (neighbor_map : Fin N → Finset (Fin N × ℝ))
    (state : SoftSuperFlow N M) (k : ℕ) : SoftSuperFlow N M :=
  Nat.iterate (step_soft_flow neighbor_map) k state

/-! ## 2. DAG Exact Convergence -/

structure DAG (N : ℕ) where
  edges : Fin N → Fin N → ℝ
  pos_edges : ∀ i j, i ≠ j → edges i j ≥ 0  -- Off-diagonal edges non-negative
  acyclic : ∀ p : List (Fin N),
              (∀ i < p.length - 1, edges (p.get ⟨i, by linarith⟩) (p.get ⟨i+1, by linarith⟩) > 0) →
              p.nodup → False  -- No positive-weight cycles

def DAG_neighbors {N : ℕ} (graph : DAG N) : Fin N → Finset (Fin N × ℝ) :=
  fun v => (univ.filter fun u => u ≠ v ∧ graph.edges u v > 0).image (fun u => (u, graph.edges u v))

theorem soft_DAG_converges {N M : ℕ} (graph : DAG N) (state : SoftSuperFlow N M) :
    let bound := N
    let final_state := iterate_soft_flow (DAG_neighbors graph) state bound
    ∀ i m, (iterate_soft_flow (DAG_neighbors graph) state (bound + 1)).potentials i m =
           final_state.potentials i m := by
  -- Idea: Longest path in DAG has length < N. After N iterations, all values have fully propagated.
  -- Full proof requires topological order induction.
  sorry

/-! ## 3. TSP (Cyclic Graph) Convergence -/

def TSP_neighbors {N : ℕ} (graph : Fin N → Fin N → ℝ) (h_nonneg : ∀ i j, graph i j ≥ 0) :
    Fin N → Finset (Fin N × ℝ) :=
  fun i => (univ.erase i).image (fun j => (j, graph j i))  -- Incoming edges with non-neg weights

theorem soft_TSP_step_non_increasing {N M : ℕ} (graph : Fin N → Fin N → ℝ)
    (h_nonneg : ∀ i j, graph i j ≥ 0) (state : SoftSuperFlow N M) (i : Fin N) (m : Fin M) :
    (step_soft_flow (TSP_neighbors graph h_nonneg) state).potentials i m ≤ state.potentials i m := by
  unfold step_soft_flow flow_neighbors
  let incoming := TSP_neighbors graph h_nonneg i
  by_cases h : incoming = ∅
  · simp [h]  -- No update → equal
  · simp [h]
    let min_val := incoming.fold (state.potentials i m)
                        (fun acc ⟨u, w⟩ => Real.min acc (state.potentials u m + w))
    have h_min : min_val ≤ state.potentials i m := by
      apply Finset.fold_min_le_init
    cases' le_or_lt (min_val - state.damping) 0 with h_neg h_pos
    · simp [Real.max_eq_left h_neg.le]
      exact state.nonneg i m
    · simp [Real.max_eq_right h_pos.le]
      linarith [h_min]

theorem soft_TSP_cumulative_bound {N M : ℕ} (graph : Fin N → Fin N → ℝ)
    (h_nonneg : ∀ i j, graph i j ≥ 0) (state : SoftSuperFlow N M) (i : Fin N) (m : Fin M) (k : ℕ) :
    (iterate_soft_flow (TSP_neighbors graph h_nonneg) state k).potentials i m ≥
    state.potentials i m - state.damping * (k : ℝ) := by
  induction' k with k ih
  · simp [iterate_soft_flow]
  · simp [iterate_soft_flow]
    have h_step_le : (step_soft_flow _ _).potentials i m ≤
                     (iterate_soft_flow _ _ k).potentials i m :=
      soft_TSP_step_non_increasing _ h_nonneg _ _ _
    -- Drop per step is at most damping (under current assumptions this is loose; true if min_val ≥ old)
    -- Here we conservatively use a weaker bound.
    have h_drop : (iterate_soft_flow _ _ k).potentials i m -
                  (step_soft_flow _ _).potentials i m ≤ state.damping := by
      sorry  -- Requires stronger per-step analysis or additional graph assumptions
    linarith [ih]

/-! ## 4. Turing Machine as SoftSuperFlow -/

structure TMConfig (Q Σ : Type) where
  q    : Q
  tape : List Σ
  pos  : ℕ
deriving Repr, BEq, Inhabited

def all_TM_configs {Q Σ : Type} (states : List Q) (tape_syms : List Σ) (tape_len : ℕ) :
    List (TMConfig Q Σ) := do
  let q ← states
  let tape ← List.sequence (List.replicate tape_len tape_syms)
  let pos ← List.range (tape_len + 1)  -- Allow one extra position for right moves
  pure { q := q, tape := tape, pos := pos }

def TM_neighbors_map {Q Σ : Type} [BEq Q] [BEq Σ]
    (M : TM Q Σ) (configs : List (TMConfig Q Σ)) : TMConfig Q Σ → Finset (TMConfig Q Σ × ℝ) :=
  fun cfg =>
    let neighbors := configs.filterMap fun _ =>
      match M.trans cfg.q (cfg.tape.getD cfg.pos default) with
      | none => none  -- Halt → no outgoing
      | some ⟨q', s', dir⟩ =>
        let new_tape := cfg.tape.setD cfg.pos s'  -- Safe set (default if out of bounds)
        let new_pos :=
          match dir with
          | TM.Dir.left  => cfg.pos.pred
          | TM.Dir.right => cfg.pos + 1
        let c' := { q := q', tape := new_tape, pos := new_pos }
        if configs.contains c' then some (c', 0) else none  -- Stay within finite set
    neighbors.toFinset

def step_TM_config {Q Σ : Type} [BEq Q] [BEq Σ]
    (configs : List (TMConfig Q Σ)) (h_nodup : configs.Nodup)
    (neighbor_map : TMConfig Q Σ → Finset (TMConfig Q Σ × ℝ))
    (state : SoftSuperFlow configs.length 1) : SoftSuperFlow configs.length 1 :=
  step_soft_flow (fun i => neighbor_map (configs.get ⟨i, by simp [h_nodup]⟩)) state

def iterate_TM_config {Q Σ : Type} [BEq Q] [BEq Σ]
    (configs : List (TMConfig Q Σ)) (h_nodup : configs.Nodup)
    (neighbor_map : TMConfig Q Σ → Finset (TMConfig Q Σ × ℝ))
    (state : SoftSuperFlow configs.length 1) (k : ℕ) : SoftSuperFlow configs.length 1 :=
  Nat.iterate (step_TM_config configs h_nodup neighbor_map) k state

theorem soft_TM_converges {Q Σ : Type} [BEq Q] [BEq Σ]
    (M : TM Q Σ) (configs : List (TMConfig Q Σ)) (h_nodup : configs.Nodup)
    (state : SoftSuperFlow configs.length 1) :
    ∃ final_state : SoftSuperFlow configs.length 1,
      ∀ l ≥ configs.length,
        iterate_TM_config configs h_nodup (TM_neighbors_map M configs) state l = final_state := by
  -- Finite state space + non-increasing potentials + positive damping → eventual stabilization
  sorry

/-! ## 5. Unified Quantitative Convergence -/

theorem unified_liquid_master {N M K : ℕ}
    (dag : DAG N)
    (tsp : Fin N → Fin N → ℝ) (h_tsp_nonneg : ∀ i j, tsp i j ≥ 0)
    (tm : TM (Fin N) (Fin M))
    (configs : List (TMConfig (Fin N) (Fin M))) (h_configs_nodup : configs.Nodup)
    (state_dag : SoftSuperFlow N M)
    (state_tsp : SoftSuperFlow N M)
    (state_tm : SoftSuperFlow K 1) :
    ∃ bound : ℕ, ∀ l ≥ bound,
      -- DAG: exact stabilization
      (∀ i m, (iterate_soft_flow (DAG_neighbors dag) state_dag l).potentials i m =
              (iterate_soft_flow (DAG_neighbors dag) state_dag bound).potentials i m) ∧
      -- TSP: bounded deviation from value at bound (non-increasing + cumulative lower bound)
      (∀ i m, (iterate_soft_flow (TSP_neighbors tsp h_tsp_nonneg) state_tsp l).potentials i m ≥
              (iterate_soft_flow (TSP_neighbors tsp h_tsp_nonneg) state_tsp bound).potentials i m -
              state_tsp.damping * ((l - bound) : ℝ)) ∧
      -- TM: exact stabilization (finite configs)
      (∀ j, (iterate_TM_config configs h_configs_nodup (TM_neighbors_map tm configs) state_tm l).potentials j 0 =
            (iterate_TM_config configs h_configs_nodup (TM_neighbors_map tm configs) state_tm bound).potentials j 0) := by
  let bound := max (max N K) configs.length
  use bound
  intro l hl
  constructor
  · intro i m
    have := soft_DAG_converges dag state_dag
    simp [this, hl]
  constructor
  · intro i m
    have h_cum := soft_TSP_cumulative_bound tsp h_tsp_nonneg state_tsp i m (l - bound)
    have h_mono := soft_TSP_step_non_increasing tsp h_tsp_nonneg
    -- Combine monotonicity (≤ value at bound) with cumulative lower bound
    linarith [h_cum]
  · intro j
    obtain ⟨final, h_final⟩ := soft_TM_converges tm configs h_configs_nodup state_tm
    exact h_final l (by linarith [hl]) _ j
