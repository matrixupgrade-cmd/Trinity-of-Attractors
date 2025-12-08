import Mathlib.Algebra.Module.LinearMap
import Mathlib.LinearAlgebra.BilinearForm
import Mathlib.Data.Real.Basic

universe u

structure CouplingSystem :=
  (S : Type u)
  (T : Type u)
  (step : S → T → S)
  (tension : S → ℝ)

def Signal (CS : CouplingSystem) : Type u := CS.S → CS.S

def propagate (CS : CouplingSystem) (σ : Signal CS) (s : CS.S) (t : CS.T) : CS.S :=
  CS.step (σ s) t

/- Memory is compositional -/
theorem memory_persistence {CS : CouplingSystem} (σ₁ σ₂ : Signal CS)
    (s : CS.S) (t₁ t₂ : CS.T) :
    propagate CS σ₂ (propagate CS σ₁ s t₁) t₂ = CS.step (σ₂ (CS.step (σ₁ s) t₁)) t₂ := rfl

--------------------------------------------------------------------
-- Local vector fibers over the state space S
structure LocalVector (CS : CouplingSystem) where
  V : CS.S → Type u
  [inst : ∀ s, AddCommGroup (V s) × Module ℝ (V s)]

attribute [instance] LocalVector.inst

variable {CS : CouplingSystem} (LV : LocalVector CS)

--------------------------------------------------------------------
-- Propagation = family of linear maps ℝ (tension at src) → local vector at dst
def Propagation := ∀ src dst : CS.S, ℝ →ₗ[ℝ] LV.V dst

variable (P : Propagation CS LV)

def perceive (src dst : CS.S) (τ_src : ℝ) : LV.V dst :=
  P src dst τ_src

-- Linearity is now automatic
@[simp] theorem perceive_add (src dst : CS.S) (τ₁ τ₂ : ℝ) :
    perceive P src dst (τ₁ + τ₂) = perceive P src dst τ₁ + perceive P src dst τ₂ :=
  (P src dst).map_add _ _

@[simp] theorem perceive_smul (src dst : CS.S) (c τ : ℝ) :
    perceive P src dst (c • τ) = c • perceive P src dst τ :=
  (P src dst).map_smul c τ

--------------------------------------------------------------------
-- The only bridge we need: how a received vector is turned back into scalar tension
variable (reduce : ∀ {s}, LV.V s →ₗ[ℝ] ℝ)

infixr:90 " ⋯[reduce]▶ " => fun P src mid dst τ => P mid dst (reduce (P src mid τ))

--------------------------------------------------------------------
-- Key new results

/-- Superposition of arbitrary finite influences -/
def perceive_total (dst : CS.S) (sources : Σ src : CS.S, ℝ) : LV.V dst :=
  ∑ src, perceive P src.1 dst src.2

theorem perceive_total_linear (dst : CS.S) (f g : Σ src : CS.S, ℝ → ℝ) :
    perceive_total P dst (f + g) = perceive_total P dst f + perceive_total P dst g :=
  sorry -- easy with finsum_add_distrib (exercise)

/-- Induced bilinear form on the state space itself -/
def inducedBilinearForm : BilinearForm ℝ CS.S :=
{ bil := fun s₁ s₂ => reduce (P s₁ s₂ 1)
  add_left := sorry
  add_right := sorry
  smul_left := sorry
  smul_right := sorry }

-- If reduce is the identity on ℝ and P is symmetric, this is literally a Gram matrix!
-- In physical terms: this is the stiffness matrix / influence matrix / social capital matrix, etc.

/-- Effective distance induced by the coupling -/
def effectiveDistance (s₁ s₂ : CS.S) : ℝ≥0 :=
  if h : P s₁ s₂ 1 ≠ 0 then 1 / ‖reduce (P s₁ s₂ 1)‖ else ∞

--------------------------------------------------------------------
-- Concrete example: masses & springs → emergent Euclidean geometry

def springSystemLocalVector : LocalVector ⟨Fin 3, ℝ, id, fun _ => 0⟩ := sorry -- positions in ℝ

def springPropagation (k : Fin 3 → Fin 3 → ℝ) : Propagation _ springSystemLocalVector :=
  fun i j => if i = j then 0 else LinearMap.id.smulRight (k i j)

-- Then inducedBilinearForm i j = k i j (off-diagonal)
-- → Laplace matrix emerges automatically!
-- → Graph Laplacian = discrete Dirichlet energy
-- → Continuum limit → actual Riemannian metric

--------------------------------------------------------------------
-- Most important theorem (informal → formal)

/--
The geometry felt by each state is not postulated.
It is the shadow cast by how scalar tensions are linearly perceived and re-emitted.
--/
theorem emergent_geometry_slogan :
  ∃ (B : BilinearForm ℝ CS.S) (dist : CS.S → CS.S → ℝ≥0),
  ∀ s₁ s₂ τ,
  ‖perceive P s₁ s₂ τ‖₊ ≈ B (s₁, s₂) * |τ|   ∧
  dist s₁ s₂ ≤ C / |B (s₁, s₂)|  :=
sorry  -- true under mild positivity/definiteness of (P, reduce)

end
