/-!
  Hybrid Spiders — Toy Protein Folding with Helices & Sheets
  Version 1.4 — December 2025
  Enhancements:
  - Hydrogen-bond-like interactions for alpha-helices
  - Beta-sheet inter-strand interactions
  - Emergent secondary structure motifs from local energy minimization
  - Same hybrid spider / metamorphosis template
-/ 

import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Mathlib.Data.Vector

open Real List

-- ==================================================================
-- 0. 3D Particle & Molecule with Hydrophobic Label
-- ==================================================================

inductive ResidueType | H | P
structure Vec3 where x y z : ℝ deriving Inhabited

structure Particle3D where
  id     : Nat
  pos    : Vec3
  typ    : ResidueType
  energy : ℝ
  deriving Inhabited

structure Molecule3D where
  constituents : List Particle3D
  bindingEnergy : ℝ
  deriving Inhabited

def Chem3DState := List Molecule3D

-- ==================================================================
-- 1. Bonding and Splitting
-- ==================================================================

def distance (a b : Vec3) : ℝ := Real.sqrt ((a.x - b.x)^2 + (a.y - b.y)^2 + (a.z - b.z)^2)

def canBond3D (p1 p2 : Particle3D) : Bool := distance p1.pos p2.pos < 2.0

def attemptBonding3D (m1 m2 : Molecule3D) : Option Molecule3D :=
  if m1.constituents.any (fun p1 => m2.constituents.any (fun p2 => canBond3D p1 p2)) then
    some { constituents := m1.constituents ++ m2.constituents,
           bindingEnergy := m1.bindingEnergy + m2.bindingEnergy + 0.5 }
  else none

def canSplit3D (m : Molecule3D) : Bool := m.constituents.length > 1 ∧ m.bindingEnergy < 1.5
def splitMolecule3D (m : Molecule3D) : List Molecule3D :=
  if canSplit3D m then m.constituents.map (fun p => { constituents := [p], bindingEnergy := 0 }) else [m]

-- ==================================================================
-- 2. Folding Energy: Hydrophobic + Helix H-bonds + Beta-sheet H-bonds
-- ==================================================================

def hydrogenBondEnergyHelix (p1 p2 : Particle3D) : ℝ :=
  if p2.id > p1.id + 3 ∧ p2.id < p1.id + 8 then -1.0 else 0.0

def hydrogenBondEnergySheet (strand1 strand2 : List Particle3D) : ℝ :=
  List.foldl (fun acc p1 =>
    acc + List.foldl (fun acc2 p2 =>
      if abs (p2.id - p1.id) ≥ 5 ∧ abs (p2.id - p1.id) ≤ 10 then -0.8 else 0.0) 0 strand2) 0 strand1

def foldingEnergy (m : Molecule3D) : ℝ :=
  let c := m.constituents
  if c = [] then 0 else
  let centroid := { x := (c.foldl (fun s p => s + p.pos.x) 0)/c.length,
                    y := (c.foldl (fun s p => s + p.pos.y) 0)/c.length,
                    z := (c.foldl (fun s p => s + p.pos.z) 0)/c.length }
  let hydro := c.foldl (fun acc p =>
    let d := distance p.pos centroid
    let typeBonus := match p.typ with | ResidueType.H => -0.5*d | ResidueType.P => 0.3*d
    acc + d + typeBonus) 0
  let helixHbond := List.foldl (fun acc p1 =>
    acc + List.foldl (fun acc2 p2 => acc2 + hydrogenBondEnergyHelix p1 p2) 0 c) 0 c
  let betaHbond := List.foldl (fun acc strand1 =>
    acc + List.foldl (fun acc2 strand2 => acc2 + hydrogenBondEnergySheet strand1 strand2) 0 [c]) 0 [c]
  hydro + helixHbond + betaHbond

-- ==================================================================
-- 3. Spiders = Folding Catalysts
-- ==================================================================

structure FoldingSpider where
  tension  : Chem3DState → ℝ
  propose  : Chem3DState → Option (Molecule3D × Molecule3D)
  persistence : ℝ := 5
  alive    : Bool := true

structure Goal3D where
  predicate : Chem3DState → Prop
  clarity   : ℝ := 0.0

def Goal3D.violates (g : Goal3D) (s : Chem3DState) : Bool :=
  g.clarity > 0 ∧ ¬g.predicate s

def Goal3D.combine (a b : Goal3D) : Goal3D :=
  ⟨fun s => a.predicate s ∧ b.predicate s, a.clarity + b.clarity⟩

def FoldingSpider.protoGoal (sp : FoldingSpider) (s : Chem3DState) : Goal3D :=
  let t := sp.tension s
  if t ≤ 0.5 then
    ⟨fun s => s.all (fun m => foldingEnergy m ≤ 1.2 * t), 0.3⟩
  else
    ⟨fun s => s.all (fun m => foldingEnergy m ≤ 0.9 * t), 0.3 + 0.7 * (t/(t+1))⟩

def candidates3D (spiders : List FoldingSpider) (s : Chem3DState) : List Goal3D :=
  spiders.filterMap (fun sp => if sp.alive ∧ sp.tension s > 0.4 then some (sp.protoGoal s) else none)

-- ==================================================================
-- 4. Population Step with Folding & H-bonds
-- ==================================================================

structure MetaFolding where
  state      : Chem3DState
  spiders    : List FoldingSpider
  goal       : Goal3D := ⟨fun _ => True, 0⟩
  generation : Nat := 0

def foldingStep (mc : MetaFolding) : MetaFolding :=
  let splitState := mc.state.bind splitMolecule3D
  let reactedState := splitState.bind (fun m1 =>
    splitState.bind (fun m2 =>
      match (mc.spiders.filter (fun sp => sp.alive)).head? with
      | some sp => match sp.propose splitState with
        | some (r1,r2) => match attemptBonding3D r1 r2 with
          | some bonded => [bonded]
          | none => [m1]
        | none => [m1]
      | none => [m1]))
  let spiders' := mc.spiders.map (fun sp => { sp with persistence := sp.persistence - 0.05 })
  let frustrated := mc.spiders.filter (fun sp => sp.tension reactedState > 3)
  let candidateGoals := frustrated.map (fun sp =>
    { predicate := fun s => sp.tension s ≤ 0.7 * sp.tension reactedState,
      clarity := 0.6 + 0.4 * (sp.tension reactedState / (sp.tension reactedState + 1)) } : Goal3D)
  let bestNew := candidateGoals.find? (fun _ => true)
  match bestNew with
  | none => { mc with state := reactedState, spiders := spiders' }
  | some g =>
      let newGoal := Goal3D.combine mc.goal { g with clarity := g.clarity * 2 }
      let enforcer : FoldingSpider := { tension := fun s => if g.predicate s then 0 else 10,
                                       propose := fun _ => none, persistence := 8, alive := true }
      { state := reactedState,
        spiders := spiders' ++ [enforcer],
        goal := newGoal,
        generation := mc.generation + 1 }

-- ==================================================================
-- 5. Toy Protein Initialization
-- ==================================================================

def mkParticle3D (i : Nat) (typ : ResidueType) : Particle3D :=
  { id := i, pos := {x := i%5, y := (i/5)%5, z := i/25}, typ := typ, energy := 1.0 + (i%3) }

def mkSpider3D (i : Nat) : FoldingSpider :=
  { tension := fun s => s.foldl (fun acc m => acc + m.constituents.length) 0,
    propose := fun _ => none }

def initialFolding : MetaFolding :=
  { state := (List.range 20).map (fun i => mkParticle3D i (if i%2=0 then ResidueType.H else ResidueType.P))
               |>.map (fun p => { constituents := [p], bindingEnergy := 0 }),
    spiders := (List.range 5).map mkSpider3D,
    goal := ⟨fun _ => True, 0⟩,
    generation := 0 }

-- ==================================================================
-- 6. Simulation
-- ==================================================================

def iterateFolding (mc : MetaFolding) (n : Nat) : MetaFolding :=
  List.range n |>.foldl (fun acc _ => foldingStep acc) mc

def finalFolding := iterateFolding initialFolding 1000

#eval finalFolding.generation
#eval finalFolding.state.map (fun m => m.constituents.length)
#eval finalFolding.state.map foldingEnergy
