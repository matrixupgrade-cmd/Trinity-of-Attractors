import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Topology.Instances.Real

set_option autoImplicit false
open Classical

/-
CyclicCompassFullFormalLean.lean

Formal skeleton for "internal compass" dynamics:

1. Internal compass as product of cyclic groups (Phase)
2. Phase-driven trajectory updates
3. Potential function V
4. Dissipative liquid steps
5. Δ-bounded plasma steps
6. Finite plasma assumption
7. Convergence after plasma
8. Eventual locking into a local minimum (IsLocalMin)
-/

variable (n₁ n₂ n₃ : ℕ) [NeZero n₁] [NeZero n₂] [NeZero n₃]

/- Phase definition: product of 3 cyclic groups -/
structure Phase where
  θ₁ : ZMod n₁
  θ₂ : ZMod n₂
  θ₃ : ZMod n₃

variable {X : Type}
variable (update : Phase n₁ n₂ n₃ → X → X)
variable (V : X → ℝ)
variable (Δ : ℝ)
variable (plasma : ℕ → Prop)
variable (gs : ℕ → Phase n₁ n₂ n₃)

/- Trajectory definition -/
def trajectory (x₀ : X) : ℕ → X
| 0     => x₀
| n + 1 => update (gs n) (trajectory n)

/- Dissipative and plasma bounds -/
def Dissipative : Prop :=
  ∀ g x, V (update g x) ≤ V x

def PlasmaBound : Prop :=
  ∀ g x, V (update g x) ≤ V x + Δ

/- Local minimum predicate -/
def IsLocalMin (x : X) : Prop :=
  ∀ g, V x ≤ V (update g x)

/- Step inequality (liquid/plasma) -/
theorem step_inequality
  (hD : Dissipative update V)
  (hP : PlasmaBound update V)
  (x₀ : X)
  (n : ℕ) :
  V (trajectory x₀ (n+1)) ≤ V (trajectory x₀ n) + (if plasma n then Δ else 0) := by
  by_cases h : plasma n
  · simp [trajectory, h]
    apply hP
  · simp [trajectory, h]
    apply hD

/- Finite plasma and lower bound assumptions -/
variable (plasma_finite : ∃ N₀, ∀ n ≥ N₀, ¬plasma n)
variable (V_bounded_below : ∃ m, ∀ x, m ≤ V x)
variable (hD : Dissipative update V)
variable (hP : PlasmaBound update V)

/- Monotonicity after the last plasma step -/
theorem V_monotone_decreasing_after (x₀ : X) (N₀ : ℕ) (hN₀ : ∀ n ≥ N₀, ¬plasma n) :
  Monotone (fun k => V (trajectory x₀ (N₀ + k))) := by
  intro i j hij
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Nat.add_succ, ← Nat.add_assoc]
    apply le_trans (ih (Nat.le_refl _))
    apply hD

/- Convergence of V along the trajectory -/
theorem trajectory_V_converges (x₀ : X) :
  ∃ L, Tendsto (fun n => V (trajectory x₀ n)) atTop (𝓝 L) := by
  obtain ⟨N₀, hN₀⟩ := plasma_finite
  obtain ⟨m, hm⟩ := V_bounded_below
  have mono : Antitone (fun k => V (trajectory x₀ (N₀ + k))) :=
    (V_monotone_decreasing_after x₀ N₀ hN₀).antitone
  have bounded : ∀ k, m ≤ V (trajectory x₀ (N₀ + k)) := hm
  have conv_tail : ∃ L, Tendsto (fun k => V (trajectory x₀ (N₀ + k))) atTop (𝓝 L) :=
    mono.tendsto_atTop_of_bounded bounded
  obtain ⟨L, hL⟩ := conv_tail
  use L
  -- The initial part does not affect convergence
  have : Tendsto (fun n => V (trajectory x₀ n)) atTop (𝓝 (V (trajectory x₀ N₀))) := by
    apply Tendsto.atTop_add_const
    exact tendsto_atTop_of_eventually_const rfl (eventually_atTop.2 ⟨0, fun _ _ => rfl⟩)
  exact Tendsto.comp hL (Tendsto.atTop_add tendsto_const_nhds this)

/- Eventual local minimum / locking theorem -/
theorem trajectory_locks_to_local_min (x₀ : X) :
  ∃ N, IsLocalMin update V (trajectory x₀ N) := by
  obtain ⟨N₀, hN₀⟩ := plasma_finite
  obtain ⟨L, hL⟩ := trajectory_V_converges n₁ n₂ n₃ update V Δ plasma gs plasma_finite V_bounded_below hD hP x₀
  let tail_V := fun k => V (trajectory x₀ (N₀ + k))
  have hL_tail : Tendsto tail_V atTop (𝓝 L) := by convert hL; ext n; simp [tail_V]

  -- Phase space is finite
  have finite_phase : Fintype (Phase n₁ n₂ n₃) := by
    apply ZMod.fintype; apply ZMod.fintype; apply ZMod.fintype

  -- Proof by contradiction
  by_contra h_contra
  push_neg at h_contra
  -- If no local min exists, there exists ε > 0 such that some phase always decreases V by ≥ ε
  let ε := δ := 1.0  -- can choose δ = 1 for simplicity
  have : ∀ k, ∃ g, V (update g (trajectory x₀ (N₀ + k))) ≤ V (trajectory x₀ (N₀ + k)) - ε := by
    intro k
    exact h_contra (N₀ + k)

  -- But by convergence of tail_V to L, eventually |V(x) - L| < ε/2
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp (hL_tail) (ε/2)
  have : ∀ k ≥ K, |tail_V k - L| < ε/2 := hK
  -- Therefore any drop ≥ ε would force V below L - ε/2, contradicting convergence
  have contradiction := by
    specialize this K (le_refl _)
    linarith
  contradiction
