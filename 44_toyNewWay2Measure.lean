/-!
# Stochastic Hybrid Spider Simulation with Network Structure

Adds:
- Random perturbations
- Non-fully-connected graphs (adjacency)
- Fingerprint distance metrics
- Pure vs Hybrid world simulations
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic
import Mathlib.Data.Rat.Basic

open Finset

/-! ## 1. Basic Definitions -/

def N := 5
def Node := Fin N
abbrev Board := Node → Bool
abbrev Tilt := Node → ℝ
abbrev NeighborWeights := Node → Node → ℝ

def Board_example : Board := λ _ => false
def Tilt_example : Tilt := λ _ => 0.0

-- Flexible adjacency (0 = no edge, 1 = edge)
abbrev Adjacency := Node → Node → Bool

-- Example adjacency: not fully connected
def example_adj : Adjacency :=
  λ i j => i ≠ j ∧ (i.val + j.val) % 2 = 0

-- Weighted adjacency
def example_weights : NeighborWeights :=
  λ i j => if example_adj i j then 0.1 + 0.05 * j.val else 0.0

/-! ## 2. Perturbations and Stochasticity -/

inductive Perturbation
| virus
| social

-- Add randomness (0 ≤ r ≤ 1)
def stochastic_flip (p : ℝ) (r : ℝ) : Bool := r < p

-- Threshold function
def threshold_weighted (p : Perturbation) (tilt : ℝ) : ℕ :=
  match p with
  | Perturbation.virus => (5.0 * (1.0 - tilt)).ceil.toNat
  | Perturbation.social => (3.0 * (1.0 - tilt)).ceil.toNat

/-! ## 3. Tilt Update Function -/

def update_tilt_weighted (b : Board) (tilt : Tilt) (weights : NeighborWeights) (i : Node) : ℝ :=
  let influence := Finset.univ.sum (λ j => weights i j * (if b j then 1.0 else 0.0))
  (tilt i + influence).min 1.0

/-! ## 4. Step Function with Stochasticity -/

def step_board_stochastic (b : Board) (tilt : Tilt) (weights : NeighborWeights)
                          (step_num : ℕ) (perturbs : List Perturbation) (rand : Node → ℝ)
                          : Board × Tilt :=
  let b' := λ i =>
    if b i then true
    else perturbs.any (λ p => stochastic_flip 0.5 (rand i))  -- simple random threshold
  let tilt' := λ i => update_tilt_weighted b' tilt weights i
  (b', tilt')

/-! ## 5. Multi-step Iteration -/

def board_iterate_stochastic : ℕ → Board → Tilt → NeighborWeights → List Perturbation → (Node → ℝ) → Board × Tilt
| 0, b, t, _, _, _ => (b, t)
| n+1, b, t, w, ps, rand =>
  let (b', t') := step_board_stochastic b t w n ps rand
  board_iterate_stochastic n b' t' w ps rand

/-! ## 6. Fingerprints -/

structure AsymmetryFingerprint :=
  (affected : Finset Node)
  (tilt_map : Tilt)
  (drift : ℝ)

def fingerprint (b : Board) (tilt : Tilt) : AsymmetryFingerprint :=
  let affected := filter Finset.univ (λ i => b i)
  let drift := Finset.univ.sum (λ i => if b i then 1.0 else 0.0)
  ⟨affected, tilt, drift⟩

/-! ## 7. Distance Metrics Between Fingerprints -/

def tilt_distance (f1 f2 : AsymmetryFingerprint) : ℝ :=
  Finset.univ.sum (λ i => abs (f1.tilt_map i - f2.tilt_map i))

def activation_distance (f1 f2 : AsymmetryFingerprint) : ℝ :=
  (f1.affected ∆ f2.affected).card.toReal  -- symmetric difference

/-! ## 8. Pure vs Hybrid Worlds -/

-- Pure world: fully deterministic board
def simulate_pure (steps : ℕ) : AsymmetryFingerprint :=
  board_iterate_stochastic steps Board_example Tilt_example example_weights [Perturbation.virus] (λ _ => 0.0) |> fun p => fingerprint p.1 p.2

-- Hybrid world: stochastic perturbations
def simulate_hybrid (steps : ℕ) (rand : Node → ℝ) : AsymmetryFingerprint :=
  board_iterate_stochastic steps Board_example Tilt_example example_weights [Perturbation.virus, Perturbation.social] rand |> fun p => fingerprint p.1 p.2

/-! ## 9. Example Execution -/

def example_rand : Node → ℝ := λ i => (i.val * 17 % 100).toReal / 100.0

#eval simulate_pure 5
#eval simulate_hybrid 5 example_rand
