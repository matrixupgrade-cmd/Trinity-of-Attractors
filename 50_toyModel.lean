import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

open Finset BigOperators

/-! # Stochastic Intervention Simulation -/

def N := 12
def Node := Fin N
abbrev Board := Node -> Bool
abbrev Tilt := Node -> ℝ

/-! ## 1. Basic Drift & Fingerprint -/

def drift (b : Board) : ℝ := ∑ i, if b i then 1 else 0

structure AsymmetryFingerprint :=
  (affected : Finset Node)
  (tilt_map : Tilt)
  (drift : ℝ)

def fingerprint (b : Board) (tilt : Tilt) : AsymmetryFingerprint :=
  ⟨univ.filter (fun i => b i), tilt, drift b⟩

def fingerprint_distance (f₁ f₂ : AsymmetryFingerprint) : ℝ :=
  ∑ i, (f₁.tilt_map i - f₂.tilt_map i)^2 +
  (f₁.affected ∆ f₂.affected).card.toReal +
  (f₁.drift - f₂.drift)^2

/-! ## 2. Stochastic Update -/

def response_prob : Node → ℝ
  | ⟨0, _⟩   => 1.0
  | ⟨1, _⟩   => 1.0
  | ⟨2, _⟩   => 0.9
  | ⟨3, _⟩   => 0.8
  | ⟨4, _⟩   => 0.7
  | ⟨5, _⟩   => 0.6
  | ⟨6, _⟩   => 0.5
  | ⟨7, _⟩   => 0.4
  | ⟨8, _⟩   => 0.3
  | ⟨9, _⟩   => 0.2
  | ⟨10, _⟩  => 0.1
  | ⟨11, _⟩  => 0.0

def update_stochastic (b : Board) (thresholds : Node → ℝ) : Board :=
  fun i => b i ∨ thresholds i ≤ response_prob i

/-! ## 3. Iterated stochastic board -/

def iterated_board_stochastic (update : Board → (Node → ℝ) → Board)
    (thresholds_seq : ℕ → Node → ℝ) : ℕ → Board → Board
  | 0,     b => b
  | n + 1, b => iterated_board_stochastic update thresholds_seq n (update b (thresholds_seq n))

/-! ## 4. Persistent non-responder detection -/

def persistent_non_responders (update : Board → (Node → ℝ) → Board)
    (thresholds_seq : ℕ → Node → ℝ) (b₀ : Board) (max_iter : ℕ) : Finset Node :=
  univ.filter fun i => ∀ n ≤ max_iter, iterated_board_stochastic update thresholds_seq n b₀ i = false

/-! ## 5. Fingerprint tracking over iterations -/

def iterated_fingerprint_stochastic (update : Board → (Node → ℝ) → Board)
    (tilt_gen : Board → Tilt)
    (thresholds_seq : ℕ → Node → ℝ) : ℕ → Board → AsymmetryFingerprint
  | n, b => fingerprint (iterated_board_stochastic update thresholds_seq n b)
                       (tilt_gen (iterated_board_stochastic update thresholds_seq n b))

/-! ## 6. Example: Tilt generator and thresholds -/

def zero_tilt (_ : Board) : Tilt := fun _ => 0

def thresholds_example (_ : ℕ) : Node → ℝ := fun _ => 0.5

/-! ## 7. Run a small simulation -/

def b₀ : Board := fun _ => false

#eval persistent_non_responders update_stochastic thresholds_example b₀ 5
#eval iterated_fingerprint_stochastic update_stochastic zero_tilt thresholds_example 5 b₀
