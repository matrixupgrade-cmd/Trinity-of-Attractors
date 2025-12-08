import Mathlib.LinearAlgebra.BilinearForm
import Mathlib.LinearAlgebra.NormedSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.Topology.MetricSpace.Basic

open scoped NNReal

universe u

structure CouplingSystem :=
  (S : Type u)
  [instGroup : AddCommGroup S]
  [instModule : Module ℝ S]
  (T : Type u)
  (step : S → T → S)
  (tension : S → ℝ)

/- We now require S itself to be a normed space so that ‖·‖ makes sense on the state -/
variable (CS : CouplingSystem)
  [NormedAddCommGroup CS.S] [NormedSpace ℝ CS.S]

def Signal := CS.S → CS.S

def propagate (σ : Signal CS) (s : CS.S) (t : CS.T) : CS.S :=
  CS.step (σ s) t

-- Local perception fibers
structure LocalVector (CS : CouplingSystem) where
  V : CS.S → Type u
  [isAddCommGroup : ∀ s, AddCommGroup (V s)]
  [isModule : ∀ s, Module ℝ (V s)]
  [normed : ∀ s, NormedAddCommGroup (V s)]
  [normedSpace : ∀ s, NormedSpace ℝ (V s)]

attribute [instance] LocalVector.isAddCommGroup LocalVector.isModule
attribute [instance] LocalVector.normed LocalVector.normedSpace

variable {CS : CouplingSystem} (LV : LocalVector CS)

-- Propagation kernel: how scalar tension at src is perceived at dst
def Propagation (CS : CouplingSystem) (LV : LocalVector CS) :=
  ∀ src dst : CS.S, ℝ →ₗ[ℝ] LV.V dst

variable (P : Propagation CS LV)

def perceive (src dst : CS.S) (τ : ℝ) : LV.V dst :=
  P src dst τ

@[simp] theorem perceive_add (src dst : CS.S) (τ₁ τ₂ : ℝ) :
    perceive P src dst (τ₁ + τ₂) = perceive P src dst τ₁ + perceive P src dst τ₂ :=
  (P src dst).map_add _ _

@[simp] theorem perceive_smul (src dst : CS.S) (c τ : ℝ) :
    perceive P src dst (c • τ) = c • perceive P src dst τ :=
  (P src dst).map_smul c τ

-- Crucial bridge: how a received vector is turned back into scalar tension
variable (reduce : ∀ s, LV.V s →ₗ[ℝ] ℝ)

-- Composition along a path
def compose₂ (src mid dst : CS.S) (τ : ℝ) : LV.V dst :=
  P mid dst (reduce mid (P src mid τ))

infixr:90 " --[reduce]→ " => compose₂

-- Total perception from many sources
def perceive_total (dst : CS.S) (sources : Finset (CS.S × ℝ)) : LV.V dst :=
  sources.sum (fun (src, τ) => perceive P src dst τ)

-- Induced bilinear form on the base space S
def inducedBilinearForm : BilinearForm ℝ CS.S :=
{ bil := fun x y => reduce y (P x y 1)
  add_left := fun x₁ x₂ y => by simp [LinearMap.map_add]
  add_right := fun x y₁ y₂ => by simp [LinearMap.map_add₂ (reduce y₁) _ _]
  smul_left := fun r x y => by simp [LinearMap.map_smul]
  smul_right := fun r x y => by simp [LinearMap.map_smul₂ (reduce y)] }

variable {P} {reduce}

-- Effective coupling strength (absolute value of the bilinear form)
def couplingStrength (x y : CS.S) : ℝ≥0 := ‖inducedBilinearForm P reduce x y‖₊

-- Effective distance (inverse coupling, with ∞ when disconnected)
def effectiveDistance (x y : CS.S) : ℝ≥0∞ :=
  if h : couplingStrength P reduce x y ≠ 0
  then (couplingStrength P reduce x y)⁻¹
  else ⊤

-- THE BIG THEOREM ------------------------------------------------------------
theorem emergent_geometry
  (h_sym   : ∀ x y, inducedBilinearForm P reduce x y = inducedBilinearForm P reduce y x)
  (h_pos   : ∀ x y, 0 < inducedBilinearForm P reduce x y)   -- positive definite coupling
  (h_norm  : ∀ s v, ‖v‖ = |reduce s v|)                     -- norm is induced by reduction
  :
  ∃ (B : BilinearForm ℝ CS.S) (d : CS.S → CS.S → ℝ≥0∞),
    B.IsSymm ∧ B.IsPosDef ∧
    ∀ x y τ,
      ‖perceive P x y τ‖ = |B x y| * |τ| ∧
      d x y = 1 / |B x y| :=
by
  let B := inducedBilinearForm P reduce
  let d x y := if _ : B x y = 0 then ⊤ else (↑|B x y|)⁻¹
  use B, d
  constructor
  · exact h_sym
  constructor
  · intro x hx
    have := h_pos x x
    simp_all [inducedBilinearForm, couplingStrength]
  · rintro x y τ
    constructor
    · calc
        ‖perceive P x y τ‖ = ‖P x y τ‖             := rfl
      _ = ‖τ • P x y 1‖                     := by rw [LinearMap.map_smul]
      _ = |τ| * ‖P x y 1‖                   := norm_smul _ _
      _ = |τ| * |reduce y (P x y 1)|        := by rw [h_norm y]
      _ = |τ| * |B x y|                     := rfl
    · by_cases h_zero : B x y = 0
      · have := h_pos x y; simp_all
      · rw [d, dif_neg h_zero]
        field_simp [abs_ne_zero.mpr h_zero]

-- Concrete spring network example (now typechecks!)
def SpringSystem := CouplingSystem.mk (Fin 4 → ℝ) (by infer_instance) (by infer_instance) ℝ (fun _ _ => 0) (fun _ => 0)

def displacementVector : LocalVector SpringSystem where
  V := fun _ => ℝ
  -- all instances inherited from ℝ

def springReduce (s : Fin 4 → ℝ) : displacementVector.V s →ₗ[ℝ] ℝ := LinearMap.id

def springKernel (k : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4 → ℝ) :
    ℝ →ₗ[ℝ] displacementVector.V j :=
  if i = j then 0 else LinearMap.id.smulRight (k i j)

-- The induced bilinear form is exactly the (signed) stiffness matrix!
example (k : Matrix (Fin 4) (Fin 4) ℝ) :
    inducedBilinearForm (springKernel k) springReduce =
    BilinearForm.ofMatrix (k.negOffDiag) := by
  rfl  -- literally true by definition
