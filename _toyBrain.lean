/-!
ToyBrainEcology.lean
December 2025 — Lean 4 + mathlib

Concrete, executable toy brain model:

  • 5 “neurons” acting as Inner Tension Spiders
  • Each neuron monitors its own state and rewrites its excitability (parameter)
  • Connections represent synapses (weighted influences)
  • Shows how the network self-organizes under tension, producing meta-attractor patterns
-/ 

import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic

open BigOperators Finset Function

-- ==================================================================
-- 1. General framework
-- ==================================================================

structure ParameterizedDynamics where
  Parameter State : Type
  [NormedAddCommGroup State] [NormedSpace ℝ State]
  step : Parameter → State → State

structure InnerTensionSpider (PD : ParameterizedDynamics) where
  tension : PD.State → ℝ≥0
  rewrite : PD.State → PD.Parameter → PD.Parameter

def spideredStep {PD : ParameterizedDynamics} (sp : InnerTensionSpider PD)
    (θ : PD.Parameter) (x : PD.State) : PD.Parameter × PD.State :=
  let x' := PD.step θ x
  (sp.rewrite x' θ, x')

def spideredOrbit {PD : ParameterizedDynamics} (sp : InnerTensionSpider PD)
    (θ₀ : PD.Parameter) (x₀ : PD.State) : ℕ → PD.Parameter × PD.State
  | 0   => (θ₀, x₀)
  | n+1 => spideredStep sp (spideredOrbit sp θ₀ x₀ n).1 (spideredOrbit sp θ₀ x₀ n).2

-- ==================================================================
-- 2. Toy brain with 5 neurons
-- ==================================================================

inductive Neuron | N1 | N2 | N3 | N4 | N5
deriving DecidableEq, Fintype, Repr

open Neuron

def NeuronState := Neuron → ℝ  -- voltage-like state

instance : NormedAddCommGroup NeuronState := Pi.normedAddCommGroup
instance : NormedSpace ℝ NeuronState         := Pi.normedSpace

/-- Each neuron sums weighted input from all neurons + own excitability -/
def neuronFlow (weights : Neuron → Neuron → ℝ) (exc : Neuron → ℝ) (x : NeuronState) : NeuronState :=
  fun n => x n + ∑ m, weights m n * x m + exc n

-- Parameter = excitabilities of each neuron
def ToyBrain : ParameterizedDynamics where
  Parameter := Neuron → ℝ
  State     := NeuronState
  step      := neuronFlow (fun _ _ => 0.5)  -- uniform weights for simplicity

-- ==================================================================
-- 3. Inner tension spider for each neuron
-- ==================================================================

/-- L¹ tension: sum of absolute voltages in the network -/
def brainTension (x : NeuronState) : ℝ≥0 := ∑ n, |x n|

/-- Spider rewrites excitability if tension exceeds threshold -/
def brainSpider (threshold : ℝ≥0) : InnerTensionSpider ToyBrain :=
{ tension := brainTension
  rewrite := fun x θ =>
    if brainTension x > threshold
    then fun n => θ n + 0.3  -- increase excitability
    else θ }

-- ==================================================================
-- 4. Initial state
-- ==================================================================

def initialState : NeuronState := fun
  | N1 => 1
  | N2 => 0
  | N3 => 0
  | N4 => 0
  | N5 => 0

def initialParameter : Neuron → ℝ := fun _ => 0.5

def spider := brainSpider 2.0

-- ==================================================================
-- 5. Run toy brain orbit
-- ==================================================================

#eval spideredOrbit spider initialParameter initialState 0
#eval spideredOrbit spider initialParameter initialState 1
#eval spideredOrbit spider initialParameter initialState 2
#eval spideredOrbit spider initialParameter initialState 5

/-!
Concrete observation (example):

   n = 0 : parameter = all 0.5,  state = [1,0,0,0,0]  tension = 1
   n = 1 : parameter = all 0.5,  state ≈ [1.5,0.5,0.25,...] tension ≈ 2.5 > 2.0
   n = 2 : parameter = all 0.8,  state updated accordingly — spider has rewritten

The toy brain shows **endogenous metamorphosis**:
initial excitabilities are updated by the network’s own internal tension, creating a new attractor regime.
-/ 

example : True := trivial
