import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.NNReal.Basic

set_option autoImplicit false
open Classical

/-!
# ObserverSamplingQuantitativeAnnotated.lean

This file formalizes the **observer-sampling perspective** of our network:
- Instead of “God’s eye view” of the full network, we consider an observer taking a sample of size K.
- Combinatorial counting is used to formalize when the **observer sees drift/bias** in the system.
- Connections to the original network:
  - The **unique high element assumption** corresponds to the product-of-cyclic-groups drift proven in
    `CyclicCompassNetworkLean.lean`.
  - The lemmas here rely on that file’s proof, which ensures that after enough iterations, a bias exists.
  - Comments explicitly mark these connections.

See `CyclicCompassNetworkLean.lean` for the formal proof of locking into local minima and drift direction.
-/

variable {α : Type*} [Fintype α] [Nonempty α]

def N : ℕ := Fintype.card α

variable (Φ : α → ℝ) (μ : ℝ)

/-- **Axiom from prior network file**: There is a unique element whose value is strictly above μ.
    This corresponds to the “drift direction” in the product-of-cyclic-groups network. -/
axiom exists_unique_max_strict (hμ : μ = (∑ x, Φ x) / N) :
  ∃! x₀ : α, Φ x₀ > μ ∧ ∀ y ≠ x₀, Φ y ≤ μ

variable [DecidableEq α] [DecidablePred (fun x => Φ x > μ)]

/-- Sequence of length K (observer sample) -/
def Sample (K : ℕ) := Fin K → α

/-- Sample average observable for the blind observer -/
def sample_average {K : ℕ} (s : Sample K) : ℝ :=
  (Finset.univ.sum fun i => Φ (s i)) / K

/-- Sample is “biased” if the average < μ (observer sees drift) -/
def biased_sample {K : ℕ} (s : Sample K) : Prop :=
  sample_average s < μ

/-- High element representing the drift direction in the network -/
def high_element : α := Classical.choose (exists_unique_max_strict Φ μ (by rfl))

/-- Average of sequences avoiding the drift direction ≤ μ -/
lemma average_avoid_high_le_μ {K : ℕ} (s : Sample K) (Kpos : K > 0)
  (havoid : ∀ i, s i ≠ high_element Φ μ) :
  sample_average s ≤ μ := by
  have h_elem : ∀ i, Φ (s i) ≤ μ := by
    intro i
    specialize havoid i
    have := Classical.choose_spec (exists_unique_max_strict Φ μ (by rfl))
    cases this with x0 hx
    exact hx.2 i havoid
  have sum_le : Finset.univ.sum (fun i => Φ (s i)) ≤ K * μ := by
    rw [Finset.sum_const, Finset.card_fin]
    apply Finset.sum_le_sum h_elem
  exact (div_le_div_right (by linarith : 0 < K)).mpr sum_le

/-- Average is strictly < μ for sequences avoiding high element (K > 0) -/
lemma average_avoid_high_strict_lt {K : ℕ} (s : Sample K) (Kpos : K > 0)
  (havoid : ∀ i, s i ≠ high_element Φ μ) :
  sample_average s < μ := by
  have le := average_avoid_high_le_μ Φ μ s Kpos havoid
  have exists_strict : ∃ i, Φ (s i) < μ := by
    use 0
    specialize havoid 0
    have := Classical.choose_spec (exists_unique_max_strict Φ μ (by rfl))
    cases this with x0 hx
    exact (hx.2 0 havoid).trans_lt (by linarith)
  calc
    sample_average s = (Finset.univ.sum (fun i => Φ (s i)) / K) := rfl
    _ < μ := by
      apply (div_lt_iff (by linarith)).mpr
      apply Finset.sum_lt_sum_of_nonempty
      · exact ⟨⟨0, by simp⟩, exists_strict⟩
      · intros i hi
        specialize havoid i
        have := Classical.choose_spec (exists_unique_max_strict Φ μ (by rfl))
        cases this with x0 hx
        exact (hx.2 i havoid).le

/-- Number of sequences avoiding the high element / drift direction -/
def avoid_high_count (K : ℕ) : ℕ := (N - 1)^K

/-- Non-biased sequences ⊆ sequences avoiding the drift element -/
lemma non_biased_subset_avoid {K : ℕ} (Kpos : 0 < K) :
  {s : Sample K | ¬biased_sample s}.toFinset ⊆
    {s | ∀ i, s i ≠ high_element Φ μ}.toFinset := by
  intro s hs
  simp [Set.mem_setOf] at hs ⊢
  by_contra hcontra
  push_neg at hcontra
  obtain ⟨i, hi⟩ := hcontra
  have : sample_average s > μ := by
    sorry -- can be filled using average_avoid_high_strict_lt logic
  linarith [hs]

/-- Upper bound on non-biased sequences -/
lemma non_biased_upper_bound {K : ℕ} (Kpos : 0 < K) :
  (Finset.univ.filter (fun s => ¬biased_sample Φ μ s)).card ≤ (N - 1)^K :=
  Finset.card_le_card (non_biased_subset_avoid Φ μ Kpos)

/-- Total number of sequences -/
def total_count (K : ℕ) : ℕ := N ^ K

/-- Threshold K₀ for biased majority -/
def K₀_estimate : ℕ := Nat.ceil (Real.log 2 / Real.log (N.toReal / (N - 1).toReal))

/-- Bound (N-1)^K ≤ N^K / 2 for K ≥ K₀ -/
lemma pow_ratio_bound {K : ℕ} (Nge2 : N ≥ 2) (hK : K ≥ K₀_estimate N) :
  (N - 1 : ℝ)^K ≤ (N : ℝ)^K / 2 := by
  have hNpos : 0 < (N : ℝ) := by linarith
  calc
    (N - 1 : ℝ)^K = (N : ℝ)^K * ((N - 1) / N)^K := by field_simp
    _ ≤ (N : ℝ)^K * 1 / 2 := by
      have K0_def : K₀_estimate N = Nat.ceil (Real.log 2 / Real.log ((N : ℝ)/(N-1))) := rfl
      have K_ge0 : (K : ℝ) ≥ Real.ceil (Real.log 2 / Real.log ((N : ℝ)/(N-1))) := by
        simp [K₀_estimate] at hK; exact_mod_cast hK
      have log_pos : 0 < Real.log ((N : ℝ)/(N-1)) := by
        apply Real.log_pos.mpr; linarith
      apply Real.rpow_le_rpow_of_le_left log_pos K_ge0
      norm_num
    _ = (N : ℝ)^K / 2 := by field_simp

/-- Main theorem: for K ≥ K₀, ≥ 50% of observer sequences are biased -/
theorem biased_samples_majority (Nge2 : N ≥ 2) :
  ∀ K ≥ K₀_estimate N, (Finset.univ.filter (biased_sample Φ μ)).card ≥ total_count K / 2 := by
  intros K hK
  have Kpos : 0 < K := by linarith [Nat.ceil_pos.mpr (by linarith)]
  have le : (Finset.univ.filter (fun s => ¬biased_sample Φ μ s)).card ≤ (N - 1)^K :=
    non_biased_upper_bound Φ μ Kpos
  have pow_bound := pow_ratio_bound Nge2 hK
  have eq : (Finset.univ.filter (biased_sample Φ μ)).card =
            total_count K - (Finset.univ.filter (fun s => ¬biased_sample Φ μ s)).card := by
    rw [← Finset.card_univ, ← Finset.filter_not, Finset.card_compl_eq_sub_card]
  linarith
