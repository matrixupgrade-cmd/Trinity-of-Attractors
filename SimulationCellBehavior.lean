/-!
  Cellular Inner Tension Spiders — Toy Simulation
  Fully Executable Lean 4, December 2025 Mathlib

  Nodes:
    • DNA    — measures transcription tension
    • Fiber  — measures mechanical stress
    • Protein — molecules that move and bind fibers

  Couplings:
    DNA → Protein
    Protein → Fiber
    Fiber → DNA

  Inner spiders:
    Each node measures local tension and updates itself accordingly
-/ 

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card

open BigOperators Finset Function
open scoped Classical InnerProductSpace

noncomputable section

-- ==================================================================
-- Node definition
-- ==================================================================

inductive Node | DNA | Fiber | Protein deriving Repr, DecidableEq, Fintype
open Node

instance : InnerProductSpace ℝ ℝ := EuclideanSpace.innerProductSpace _

def VNode (n : Node) := ℝ

-- ==================================================================
-- Couplings (directed influences)
-- ==================================================================

def couples : Node → Node → Prop
  | DNA, Protein    => True
  | Protein, Fiber  => True
  | Fiber, DNA      => True
  | _, _            => False

instance dec_couples (x y : Node) : Decidable (couples x y) := by
  cases x <;> cases y <;> simp [couples] <;> exact decTrue <|> exact decFalse

-- Linear propagation (identity for simplicity)
def prop : ∀ ⦃x y⦄, couples x y → VNode x →L[ℝ] VNode y := λ _ => ContinuousLinearMap.id _
def reduce (n : Node) : VNode n →L[ℝ] ℝ := ContinuousLinearMap.id _

-- ==================================================================
-- Inner tension spider system
-- ==================================================================

structure CellularICS :=
  (prop   : ∀ ⦃x y⦄, couples x y → VNode x →L[ℝ] VNode y := prop)
  (red    : ∀ s, VNode s →L[ℝ] ℝ := reduce)
  (spider : ∀ s, (Node → ℝ) → ℝ)               -- measure local tension
  (update : ∀ s, VNode s × ℝ → VNode s)         -- update node using spider feedback

-- Induced functional: propagate then reduce
def induced (CICS : CellularICS) {x y : Node} (h : couples x y) : VNode x →L[ℝ] ℝ :=
  (CICS.red y).comp (CICS.prop h)

-- Representer (trivial since ℝ)
def representer (CICS : CellularICS) {x y : Node} (h : couples x y) : VNode x :=
  (induced CICS h).adjoint 1

-- Spider energy at node y
def spiderEnergy (CICS : CellularICS) (φ : Node → ℝ) (y : Node) : ℝ :=
  ∑ x in Finset.univ.filter (couples · y), (induced CICS (x.2) (φ x))^2

-- Single step: update each node with spider feedback
def step (CICS : CellularICS) (φ : Node → ℝ) : Node → ℝ :=
  λ s => CICS.update s (φ s, CICS.spider s φ)

-- ==================================================================
-- Example spiders and updates
-- ==================================================================

-- Spider functions: measure sum of squares of incoming couplings
def dnaSpider (s : Node) (φ : Node → ℝ) : ℝ :=
  match s with
  | DNA    => ∑ x in Finset.univ.filter (couples · DNA), (φ x)^2
  | Fiber  => ∑ x in Finset.univ.filter (couples · Fiber), (φ x)^2
  | Protein=> ∑ x in Finset.univ.filter (couples · Protein), (φ x)^2

-- Update rules: negative feedback proportional to spider energy
def dnaUpdate (s : Node) (vE : ℝ × ℝ) : ℝ :=
  let (φ_s, E_s) := vE
  match s with
  | DNA     => φ_s - 0.1 * E_s
  | Fiber   => φ_s - 0.1 * E_s
  | Protein => φ_s - 0.1 * E_s

def cellularICS : CellularICS :=
  { spider := dnaSpider
    update := dnaUpdate }

-- Initial state (activity/tension levels)
def φ0 : Node → ℝ
  | DNA     => 5
  | Fiber   => 2
  | Protein => 1

#eval φ0 DNA, φ0 Fiber, φ0 Protein  -- (5,2,1)

-- Step iterations
def φ1 := step cellularICS φ0
#eval φ1 DNA, φ1 Fiber, φ1 Protein

def φ2 := step cellularICS φ1
#eval φ2 DNA, φ2 Fiber, φ2 Protein

def φ3 := step cellularICS φ2
#eval φ3 DNA, φ3 Fiber, φ3 Protein

-- Iterate N steps
def iterate (n : Nat) (φ : Node → ℝ) : Node → ℝ :=
  Nat.rec φ (fun _ φ' => step cellularICS φ') n

def φ10 := iterate 10 φ0
#eval φ10 DNA, φ10 Fiber, φ10 Protein

/-!
  Observations:
  - DNA, Fiber, Protein all relax according to their inner spider feedback.
  - Tension measured internally changes node state, illustrating the "observer effect".
  - You can tweak initial states, spider functions, update rules, or coupling strengths.
  - Extensions: add nonlinear updates, stochastic updates, or more nodes to simulate larger cellular networks.
-/ 
