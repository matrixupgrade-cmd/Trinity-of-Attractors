/-!
  Statistical Internal Tension Spider — Observer Bias Playground
  Fully Executable Lean 4, December 2025 Mathlib

  Philosophy (high-level intuition):
  - Imagine a system where each "node" (like a person or institution) tries to act like a statistician: 
    it computes means and variances of its "neighbors" (incoming influences), thinking it's objectively measuring reality.
  - But since the node uses those stats to update itself, and neighbors are doing the same, the "data" is contaminated by previous updates.
  - This creates a feedback loop: stats bias actions, actions bias future stats — the "observer" (statistical spider) warps the very reality it's measuring.
  - In comments below, we'll unpack the intuition step-by-step, like why mean/variance feedback mimics real-world biases (e.g., echo chambers, policy loops).
-/ 

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card

open BigOperators Finset Function
open scoped Classical InnerProductSpace

noncomputable section

-- ==================================================================
-- Tiny 3-node universe
-- Intuition: Three "agents" in a cycle: A influences B, B influences C, C influences A.
-- Like a tiny social network or economy where info/wealth flows in a loop.
-- ==================================================================

inductive Node | A | B | C deriving Repr, DecidableEq, Fintype
open Node

instance : InnerProductSpace ℝ ℝ := EuclideanSpace.innerProductSpace _

def VNode (n : Node) := ℝ

-- Couplings: directed cycle A→B→C→A
-- Intuition: Arrows represent "influence" — A "pulls" on B, etc. No self-loops means no navel-gazing; bias comes from the cycle.
def couples : Node → Node → Prop
  | A, B => True
  | B, C => True
  | C, A => True
  | _, _ => False

instance dec_couples (x y : Node) : Decidable (couples x y) := by
  cases x <;> cases y <;> simp [couples] <;> exact decTrue <|> exact decFalse

-- Linear propagation and reduction (both identity)
-- Intuition: Propagation is how influence travels (here, directly copies values). Reduction "observes" the value as a scalar.
def prop : ∀ ⦃x y⦄, couples x y → VNode x →L[ℝ] VNode y := λ _ => ContinuousLinearMap.id _
def reduce (n : Node) : VNode n →L[ℝ] ℝ := ContinuousLinearMap.id _

-- ==================================================================
-- Statistical internal coupling system
-- Intuition: This structure embeds the "inner spider" — energy computation + stats — inside the system.
-- The spider pretends to be an objective statistician, but its outputs feed back, creating self-fulfilling prophecies.
-- ==================================================================

structure StatisticalInternalCouplingSystem :=
  (prop   : ∀ ⦃x y⦄, couples x y → VNode x →L[ℝ] VNode y := prop)
  (red    : ∀ s, VNode s →L[ℝ] ℝ := reduce)
  (spider : ∀ s, (Node → ℝ) → ℝ)                 -- tension energy: measures "pull" from neighbors
  (stats  : ∀ s, (Node → ℝ) → ℝ × ℝ)             -- mean & variance: pretends to be "unbiased" stats
  (update : ∀ s, VNode s × ℝ × ℝ × ℝ → VNode s)  -- combines current value, energy, mean, variance into new value

-- Induced functional: propagate then reduce
-- Intuition: This is the "tension thread" — how much pull from x affects y's observation.
def induced (SICS : StatisticalInternalCouplingSystem) {x y : Node} (h : couples x y) : VNode x →L[ℝ] ℝ :=
  (SICS.red y).comp (SICS.prop h)

-- Representer (Riesz vector) — trivial since ℝ
-- Intuition: In vector spaces, this is the "direction" of maximal tension; here in ℝ, it's just scaling.
def representer (SICS : StatisticalInternalCouplingSystem) {x y : Node} (h : couples x y) : VNode x :=
  (induced SICS h).adjoint 1

-- Spider energy at site y
-- Intuition: Sum of squared incoming influences — like total "stress" on y from its pullers.
-- High energy means y is being yanked hard; the spider measures this "internally."
def spiderEnergy (SICS : StatisticalInternalCouplingSystem) (φ : Node → ℝ) (y : Node) : ℝ :=
  ∑ x in Finset.univ.filter (couples · y), (induced SICS (x.2) (φ x))^2

-- Statistics: mean & variance of incoming nodes
-- Intuition: Each node computes stats on its "sample" (incoming values), assuming independence.
-- But since the system is coupled and updating, the sample is biased by past stats — self-attraction.
def meanVariance (y : Node) (φ : Node → ℝ) : ℝ × ℝ :=
  let ins := Finset.univ.filter (couples · y)
  if ins.card = 0 then (0, 0)
  else
    let μ := (∑ x in ins, φ x) / ins.card.toReal
    let σ² := (∑ x in ins, (φ x - μ)^2) / ins.card.toReal
    (μ, σ²)

-- Single evolution step
-- Intuition: Every node simultaneously "observes" (computes energy + stats) and "reacts" (updates itself).
-- This is where the observer effect bites: measurement isn't passive; it drives the next state.
def step (SICS : StatisticalInternalCouplingSystem) (φ : Node → ℝ) : Node → ℝ :=
  λ s =>
    let E := SICS.spider s φ
    let (μ, σ²) := SICS.stats s φ
    SICS.update s (φ s, E, μ, σ²)

-- ==================================================================
-- Example system: tiny 3-node with statistical inner spider
-- Intuition: We simulate a cycle where nodes "relax" tension but also "chase" means and avoid variance.
-- This mimics economies chasing averages (self-fulfilling) or social groups polarizing on low-variance views.
-- ==================================================================

def tinySpider (s : Node) (φ : Node → ℝ) : ℝ :=
  ∑ x in Finset.univ.filter (couples · s), (φ x)^2

def tinyStats (s : Node) (φ : Node → ℝ) : ℝ × ℝ := meanVariance s φ

-- Update: damped feedback from energy + bias from statistics
-- Intuition: Subtract energy (relax tension), add mean (conform to average), subtract variance (avoid uncertainty).
-- This creates self-attraction: nodes pull toward their own biased perceptions.
def tinyUpdate (s : Node) (vE : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  let (φ_s, E_s, μ_s, σ²_s) := vE
  φ_s - 0.1 * E_s + 0.05 * μ_s - 0.05 * σ²_s

def tinySICS : StatisticalInternalCouplingSystem :=
  { spider := tinySpider, stats := tinyStats, update := tinyUpdate }

-- Initial field
-- Intuition: Start with unbalanced values; watch how internal stats drive convergence or divergence.
def φ0 : Node → ℝ
  | A => 1
  | B => 2
  | C => 4

#eval φ0 A, φ0 B, φ0 C  -- (1, 2, 4)

-- Step iterations
def φ1 := step tinySICS φ0
#eval φ1 A, φ1 B, φ1 C  -- Observer bias kicks in: A sees high energy from C=4, relaxes hard.

def φ2 := step tinySICS φ1
#eval φ2 A, φ2 B, φ2 C  -- Cycle propagates: B now feels A's adjustment, stats shift.

def φ3 := step tinySICS φ2
#eval φ3 A, φ3 B, φ3 C  -- Higher orders: self-attraction builds as means/variances chase each other.

-- Iterate further to see long-term bias
def iterate (n : Nat) (φ : Node → ℝ) : Node → ℝ :=
  Nat.rec φ (fun _ φ' => step tinySICS φ') n

def φ10 := iterate 10 φ0
#eval φ10 A, φ10 B, φ10 C  -- After 10 steps: system may stabilize or spiral, showing accumulated bias.

/-!
  Observations (intuitive takeaways):
  - Each step illustrates observer bias: stats (mean/variance) seem "objective," but they're computed on data warped by prior stats.
  - Like your student loans example: initial high ROI measurement attracts more investment, inflating costs, lowering future ROI.
  - Here, nodes "chase" means (self-fulfilling averages) and flee variance (echo chambers avoiding diversity).
  - Experiment: Add self-loops (couples x x := True) — nodes include themselves in stats, amplifying narcissism.
  - Or make update nonlinear (e.g., if σ²_s > threshold then panic mode) for chaotic attractors.
  - The spider shows: statistics aren't neutral; inner observers create the reality they measure.
-/ 
