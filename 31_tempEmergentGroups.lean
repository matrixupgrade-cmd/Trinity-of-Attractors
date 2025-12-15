import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Iterate
import Mathlib.Tactic
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Group.Basic
import Mathlib.Topology.Instances.ENNReal

set_option autoImplicit false

variable {V : Type} [Fintype V] [DecidableEq V]

/- ============================================================
  1. Phases
============================================================ -/
inductive Phase := | Plasma | Liquid | Diamond

/- ============================================================
  2. Flow network & metamorphosis step
============================================================ -/
structure FlowNetwork (V : Type) [Fintype V] [DecidableEq V] :=
  (weight : V → V → ENNReal)  -- ℝ≥0∞ = ENNReal in Mathlib

-- Placeholder for MetamorphosisStep (greedy asymmetry increase from prior code)
def MetamorphosisStep (G : FlowNetwork V) : FlowNetwork V := 
  { weight := G.weight }  -- Dummy; replace with actual def

def trajectory (G₀ : FlowNetwork V) : ℕ → FlowNetwork V :=
Function.iterate MetamorphosisStep G₀

/- ============================================================
  3. Recurrent elements & orbits
============================================================ -/
def recurrent (G : FlowNetwork V) : Type :=
{ H : FlowNetwork V // ∃ N p, p > 1 ∧ ∀ n ≥ N, trajectory H n = trajectory H (n + p) }

def same_orbit (G : FlowNetwork V) (x y : recurrent G) : Prop :=
∃ k, trajectory x.val k = y.val

instance same_orbit_setoid (G : FlowNetwork V) : Setoid (recurrent G) :=
{ r := same_orbit G,
  iseqv :=
    ⟨
      fun x => ⟨0, rfl⟩,
      fun ⟨k, hk⟩ => ⟨k, hk.symm⟩,
      fun ⟨k, hk⟩ ⟨l, hl⟩ => ⟨k + l, by rw [Function.iterate_add_apply]; exact hl.trans hk⟩
    ⟩ }

def OrbitIdx (G : FlowNetwork V) := Quotient (same_orbit_setoid G)

instance OrbitIdx_fintype (G : FlowNetwork V) [Fintype (recurrent G)] : Fintype (OrbitIdx G) :=
Fintype.ofFinite _

-- Lift rep from quotient (use Classical.choice with existence)
def orbit_rep (G : FlowNetwork V) (i : OrbitIdx G) : recurrent G := 
Classical.choose (Quot.exists_rep i)

def orbit_period (G : FlowNetwork V) (x : recurrent G) : ℕ :=
let prop := x.property in Classical.choose (Classical.choose_spec prop).snd

/- ============================================================
  4. Pi-type for direct product
============================================================ -/
def Y (G : FlowNetwork V) : Type := ∀ i : OrbitIdx G, Fin (orbit_period G (orbit_rep G i))

instance Y_fintype (G : FlowNetwork V) [Fintype (recurrent G)] : Fintype (Y G) := Fintype.piFinite _

def op_Y (G : FlowNetwork V) (a b : Y G) : Y G :=
fun i => ⟨(a i).val + (b i).val % orbit_period G (orbit_rep G i), Nat.mod_lt _ _⟩

def id_Y (G : FlowNetwork V) : Y G := fun i => ⟨0, Nat.zero_lt (orbit_period G (orbit_rep G i))⟩

def inv_Y (G : FlowNetwork V) (a : Y G) : Y G :=
fun i => ⟨(orbit_period G (orbit_rep G i) - (a i).val) % orbit_period G (orbit_rep G i), Nat.mod_lt _ _⟩

def Group_Y (G : FlowNetwork V) : Group (Y G) :=
{ op := op_Y G,
  id := id_Y G,
  assoc := by 
    intros a b c i
    simp [op_Y]
    rw [Nat.add_mod, Nat.add_mod],
  left_id := by 
    intros a i
    simp [op_Y]
    rw [Nat.zero_add],
  right_id := by 
    intros a i
    simp [op_Y]
    rw [Nat.add_zero],
  inv := inv_Y G,
  left_inv := by 
    intros a i
    simp [op_Y, inv_Y]
    rw [Nat.add_mod, Nat.mod_eq_sub_mod (le_of_lt (Fin.is_lt _)), Nat.add_sub_cancel],
  right_inv := by 
    intros a i
    simp [op_Y, inv_Y]
    rw [Nat.add_mod, Nat.mod_eq_sub_mod (le_of_lt (Fin.is_lt _)), Nat.add_sub_cancel] }

/- ============================================================
  5. Iso between recurrent and Y
============================================================ -/
def to_Y (G : FlowNetwork V) (x : recurrent G) : Y G :=
fun i =>
  if h : Quotient.mk'' (same_orbit_setoid G) x = i then
    let rep := orbit_rep G i
    let prop := rep.property
    let N := Classical.choose prop
    let p := orbit_period G rep
    -- Lemma: exists unique k mod p s.t. trajectory rep.val (N + k) = x.val (since same orbit + periodic)
    let k : ℕ := Classical.choose (exists_k_trajectory G rep x N)
    ⟨k % p, Nat.mod_lt _ _⟩
  else
    ⟨0, Nat.zero_lt _⟩  -- But iso ensures all x in some i

def from_Y (G : FlowNetwork V) (y : Y G) : recurrent G :=
-- Aggregate over i, but since product, choose rep + shift per component
let main_i := default  -- Or Classical.choose some orbit
let rep := orbit_rep G main_i
let prop := rep.property
let N := Classical.choose prop
let p := orbit_period G rep
let shift := (y main_i).val
⟨trajectory rep.val (N + shift), prop⟩  -- Lemma: shifts stay recurrent

def iso_recurrent_Y (G : FlowNetwork V) : recurrent G ≃ Y G :=
{ toFun := to_Y G,
  invFun := from_Y G,
  left_inv := fun x =>
    -- Proof: find k % p recovers x via trajectory invertibility in cycle
    sorry,
  right_inv := fun y =>
    -- Proof: reconstruction via shift recovers y's components
    sorry }

/- ============================================================
  6. Metamorphosis → algebraic structure theorem
============================================================ -/
structure TrivialMonoid (X : Type) : Monoid X where
  op := fun a b => a
  id := default
  assoc := by simp
  left_id := by simp
  right_id := by simp

theorem Metamorphosis_to_algebraic_structure
  (G₀ : FlowNetwork V)
  [Fintype (recurrent G₀)] :
  ∃ φ : Phase,
    (φ = Liquid →
       ∃ (G' : Type) [Fintype G'] (A : Group G'), Nonempty (recurrent G₀ ≃ G')) ∧
    (φ = Diamond →
       ∃ (M : Monoid (FlowNetwork V)), Nonempty (∃ y N, ∀ n ≥ N, trajectory G₀ n = y)) ∧
    (φ = Plasma →
       ∀ n m, n ≠ m → trajectory G₀ n ≠ trajectory G₀ m) :=
by
  by_cases hDiamond : ∃ N, ∀ n ≥ N, trajectory G₀ n = trajectory G₀ N
  · -- Diamond case
    use Phase.Diamond
    constructor
    · intro eq; contradiction
    constructor
    · intro eq
      use TrivialMonoid (FlowNetwork V)
      rcases hDiamond with ⟨N, hN⟩
      use trajectory G₀ N, N, hN
    · intro eq; contradiction
  · by_cases hLiquid : ∃ N p, p > 1 ∧ ∀ n ≥ N, trajectory G₀ n = trajectory G₀ (n + p)
    · -- Liquid case
      use Phase.Liquid
      constructor
      · intro eq
        let G' := Y G₀
        use G', inferInstance, Group_Y G₀, ⟨iso_recurrent_Y G₀⟩
      constructor
      · intro eq; contradiction
      · intro eq; contradiction
    · -- Plasma case
      use Phase.Plasma
      constructor
      · intro eq; contradiction
      constructor
      · intro eq; contradiction
      · intros n m hnm eq
        by_cases le : n ≤ m
        · let d := m - n
          have pos : d > 0 := Nat.sub_pos_of_lt (Nat.lt_of_le_of_ne le hnm.symm)
          have per : ∀ k ≥ n, trajectory G₀ k = trajectory G₀ (k + d) := by
            intro k hk
            rw [<- eq, trajectory_add G₀ n d]
            rfl
          exact hLiquid ⟨n, d, pos, per⟩
        · let d := n - m
          have pos : d > 0 := Nat.sub_pos_of_lt (Nat.lt_of_le_of_ne (Nat.not_le.1 le) hnm)
          have per : ∀ k ≥ m, trajectory G₀ k = trajectory G₀ (k + d) := by
            intro k hk
            rw [eq, trajectory_add G₀ m d]
            rfl
          exact hLiquid ⟨m, d, pos, per⟩
