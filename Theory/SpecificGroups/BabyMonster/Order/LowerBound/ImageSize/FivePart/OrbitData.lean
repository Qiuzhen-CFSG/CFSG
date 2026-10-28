module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.FivePart.MatrixOrbit
public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.FivePart.OrbitData.Checks
public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.FivePart.OrbitData.Vectors

/-!
# A concrete 15625-point orbit candidate for the Baby Monster five-part

Write `a,b` for the outputs of the ATLAS local program `BG1-max21W1`.
The two words `a` and `(a*b^3)^8` have a 15625-point column-vector orbit
starting at the first standard basis vector. This module gives the explicit
vectors and permutations and proves distinctness, word membership and a
spanning tree. Matrix transition identities are deliberately a separate
certificate obligation, as in `MatrixOrbit.matrixOrbitCertificate_of_tree`.
No subgroup identification or proposed ATLAS order is used.

The reproducible generator checks all candidate column transitions; see
`OrbitData/source/README.md`. Its computations are not Lean proofs.
-/

@[expose] public section
namespace BabyMonster.OrderLowerBound.FivePart

/-- Number of selected words in the local ATLAS generators. -/
def generatorCount : ℕ := 2

/-- The selected generators: `a` and `(a*b^3)^8`. -/
def orbitGenerators (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1)
    (j : Fin generatorCount) : MatrixGroup :=
  let a := generators (standardA ha) (standardB hb) 0
  let b := generators (standardA ha) (standardB hb) 1
  if j.val = 0 then a else (a * b ^ 3) ^ 8

/-- Both selected words lie in the fixed standard matrix image. -/
theorem orbitGenerators_mem (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1)
    (j : Fin generatorCount) : orbitGenerators ha hb j ∈ standardImage ha hb := by
  have hg (k : Fin 2) : generators (standardA ha) (standardB hb) k ∈
      standardImage ha hb :=
    image_le_standardImage ha hb (Subgroup.subset_closure ⟨k, rfl⟩)
  dsimp only [orbitGenerators]
  split
  · exact hg 0
  · exact (standardImage ha hb).pow_mem
      ((standardImage ha hb).mul_mem (hg 0) ((standardImage ha hb).pow_mem (hg 1) 3)) 8

/-- Bits 0 through 63 are stored separately to make the distinctness check small. -/
def orbitPoint (i : Fin 15625) (k : Fin 4370) : ZMod 2 :=
  if (if k.val < 64 then (OrbitTables.signature i).getLsbD k.val
      else (OrbitTables.tail i).testBit (k.val - 64)) then 1 else 0

/-- Explicit points, base and transition permutations. -/
def orbitData : MatrixOrbitData (Fin generatorCount) where
  size := 15625
  point := orbitPoint
  base := 0
  perm := OrbitTables.perm

/-- The first 64 coordinates distinguish the points. -/
theorem orbitData_point_injective : Function.Injective orbitData.point := by
  intro i j hij
  apply OrbitTables.signature_injective
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have h := congrFun hij (⟨k, by omega⟩ : Fin 4370)
  change (if (if k < 64 then (OrbitTables.signature i).getLsbD k
      else (OrbitTables.tail i).testBit (k - 64)) then (1 : ZMod 2) else 0) =
    (if (if k < 64 then (OrbitTables.signature j).getLsbD k
      else (OrbitTables.tail j).testBit (k - 64)) then 1 else 0) at h
  rw [if_pos hk, if_pos hk] at h
  have hinj : Function.Injective (fun b : Bool => if b then (1 : ZMod 2) else 0) := by
    decide
  exact hinj h

/-- This orbit candidate supplies the full required power of five. -/
theorem five_pow_six_dvd_orbitData_size : 5 ^ 6 ∣ orbitData.size := by decide

/-- Breadth-first parent indices. -/
def parent : Fin orbitData.size → Fin orbitData.size := OrbitTables.parent

/-- The generator labelling each tree edge. -/
def edge : Fin orbitData.size → Fin generatorCount := OrbitTables.edge

/-- Every non-base parent was discovered earlier. -/
theorem parent_lt (i : Fin orbitData.size) (hi : i ≠ orbitData.base) :
    (parent i).val < i.val := OrbitTables.parent_lt i hi

/-- Each labelled tree edge is an entry of the corresponding permutation. -/
theorem parent_edge (i : Fin orbitData.size) (hi : i ≠ orbitData.base) :
    orbitData.perm (edge i) (parent i) = i := OrbitTables.parent_edge i hi

end BabyMonster.OrderLowerBound.FivePart
