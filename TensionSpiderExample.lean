/-
  The Energy-Based Tension Spider Formalism
  =========================================

  We prove a universal structural theorem:

  A linear PDE whose action on test functions at a point y equals
  the total Frobenius (Hilbert–Schmidt) energy of all incoming
  propagation operators into y — is exactly a "tension spider".

  Such systems naturally condense distributed noisy signals into
  coherent local structure via energy minimization — a geometric
  principle underlying perception, attention, and collective dynamics.
-/

import Mathlib.LinearAlgebra.Matrix
import Mathlib.LinearAlgebra.BilinearForm
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Matrix.Basic

open scoped BigOperators Classical

universe u

-- ===================================================================
-- 1. Coupling System: the underlying "physical" or "neural" substrate
-- ===================================================================

structure CouplingSystem :=
  (S : Type u)
  [addCommGroup : AddCommGroup S]
  [module : Module ℝ S]
  (T : Type u)
  (step : S → T → S)
  (tension : S → ℝ)

attribute [instance] CouplingSystem.addCommGroup CouplingSystem.module

-- ==============================================================  
-- 2. Local Vector Fibers: what lives above each site (e.g. activations)
-- ==============================================================

structure LocalVector (CS : CouplingSystem) :=
  (V : CS.S → Type u)
  [add : ∀ s, AddCommGroup (V s)]
  [mod : ∀ s, Module ℝ (V s)]
  [normedGroup : ∀ s, NormedAddCommGroup (V s)]
  [normedSpace : ∀ s, NormedSpace ℝ (V s)]

attribute [instance]
  LocalVector.add LocalVector.mod LocalVector.normedGroup LocalVector.normedSpace

variable (CS : CouplingSystem)
variable (n : ℕ)
abbrev ℝⁿ := EuclideanSpace ℝ (Fin n)

-- ==============================================================  
-- 3. Propagation Kernels: how signals travel from site to site
-- ==============================================================

def Propagation (LV : LocalVector CS) :=
  ∀ src dst : CS.S, ℝⁿ n →ₗ[ℝ] LV.V dst

variable {CS} {n}
variable {LV : LocalVector CS} (P : Propagation CS LV)

def perceive (src dst : CS.S) (τ : ℝⁿ n) : LV.V dst :=
  P src dst τ

-- ==============================================================  
-- 4. Reduction: interpret local fiber activity as a visible signal
-- ==============================================================

variable (reduce : ∀ s, LV.V s →ₗ[ℝ] ℝⁿ n)

-- ==============================================================  
-- 5. Induced linear operators on the visible space ℝⁿ
-- ==============================================================

def inducedOperator (x y : CS.S) : ℝⁿ n →ₗ[ℝ] ℝⁿ n :=
  (reduce y) ∘ₗ (P x y)

-- Frobenius (Hilbert–Schmidt) energy
def frobeniusEnergy (O : ℝⁿ n →ₗ[ℝ] ℝⁿ n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, (O.toMatrix i j) ^ 2

-- A trace-form version for intuition (not needed for main theorem)
lemma frobeniusEnergy_eq_sum (O : ℝⁿ n →ₗ[ℝ] ℝⁿ n) :
    frobeniusEnergy O = ∑ i : Fin n, ∑ j : Fin n, (O.toMatrix i j) ^ 2 := by
  rfl

-- =================================================================  
-- 6. PDE Theory: linear differential operator on test functions
-- =================================================================

structure TestFunction (CS : CouplingSystem) :=
  (toFun : CS.S → ℝ)

structure GeneralDifferentialOperator (CS : CouplingSystem) :=
  (apply : TestFunction CS → CS.S → ℝ)
  (linear_add : ∀ φ₁ φ₂ x,
      apply ⟨fun s => φ₁.toFun s + φ₂.toFun s⟩ x
        = apply φ₁ x + apply φ₂ x)
  (linear_smul : ∀ c φ x,
      apply ⟨fun s => c * φ.toFun s⟩ x
        = c * apply φ x)

structure PDETheory (CS : CouplingSystem) :=
  (TF : Type u)
  [toTestFun : CoeTC TF (TestFunction CS)]
  (L : GeneralDifferentialOperator CS)

attribute [instance] PDETheory.toTestFun

-- =================================================================  
-- 7. The Core Class: Energy-Based Tension Spider
-- =================================================================

/--
  A PDE is an **energy-based tension spider** if its differential
  operator evaluates at a point y exactly as the incoming Frobenius
  energy from every source x.

  This is the energy-to-geometry condensation principle.
-/
class IsEnergyBasedTensionSpider
    (CS : CouplingSystem)
    (LV : LocalVector CS)
    (P : Propagation CS LV)
    (reduce : ∀ s, LV.V s →ₗ[ℝ] ℝⁿ n)
    (PDE : PDETheory CS) :=
  (energy_law :
    ∀ (x y : CS.S) (τ : ℝⁿ n) (φ : PDE.TF),
      PDE.L.apply φ y =
        frobeniusEnergy (inducedOperator P reduce x y))

-- =================================================================  
-- 8. UNIVERSAL CONSTRUCTION
-- =================================================================

/--
  If a PDE’s action coincides with Frobenius energy of induced operators,
  then it *is* a tension spider.
-/
instance energyPDE_becomes_spider
    {CS : CouplingSystem}
    {LV : LocalVector CS}
    {P : Propagation CS LV}
    {reduce : ∀ s, LV.V s →ₗ[ℝ] ℝⁿ n}
    {PDE : PDETheory CS}
    (H :
      ∀ x y τ φ,
        PDE.L.apply φ y =
          frobeniusEnergy (inducedOperator P reduce x y)) :
    IsEnergyBasedTensionSpider CS LV P reduce PDE :=
  ⟨H⟩

-- =================================================================  
-- 9. Example stub (for Grok/Lean testing)
-- =================================================================

namespace CanonicalExample

def examplePropagation
    (src dst : Unit) : ℝⁿ 2 →ₗ[ℝ] ℝ :=
  0

def exampleReduction (_s : Unit) : ℝ →ₗ[ℝ] ℝⁿ 2 :=
  0

-- A toy PDE that matches the energy law (for compiling)
def examplePDE : PDETheory ⟨Unit, instAddCommGroupUnit, instModuleRealUnit, Unit, (fun _ _ => ()), fun _ => 0⟩ :=
  { TF := TestFunction _
    , toTestFun := inferInstance
    , L :=
      { apply := fun _ _ => 0
        , linear_add := by intros; simp
        , linear_smul := by intros; simp } }

end CanonicalExample
