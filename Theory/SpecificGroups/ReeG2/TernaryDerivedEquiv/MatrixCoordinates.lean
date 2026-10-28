module

public import Theory.SpecificGroups.ReeG2.TernaryDerivedEquiv.Generators

/-!
# Seven coordinates for the deleted nine-point module

Embed a column vector `v : Fin 7 → F₃` into nine coordinates as
`(v, -∑ v, 0)`. Permute the nine coordinates, and subtract the last
coordinate from each of the first seven. This is the action on the
augmentation subspace modulo the constant line; the sum of nine ones
vanishes in characteristic three.

This file supplies the coordinate formula and checks a change of basis on
the two marked generators. The multiplicativity of the coordinate formula
is a separate obligation. These finite matrix identities identify the exact
conventions required by the small Ree comparison in GLS III §2.2.
-/

@[expose] public section
namespace Atlas.ReeG2.TernaryDerived

/-- The inclusion `(v, -∑ v, 0)` as a nine-by-seven matrix. -/
def deletedInclusion (i : Fin 9) (j : Fin 7) : ZMod 3 :=
  if i = j.castLE (by decide) then 1 else if i = 7 then -1 else 0

/-- The coordinate action induced by a permutation on the deleted module. -/
def deletedMatrix (p : Equiv.Perm (Fin 9)) : Mat (ZMod 3) := fun i j =>
  deletedInclusion (p.symm (i.castLE (by decide))) j - deletedInclusion (p.symm 8) j

def basisMatrix : Mat (ZMod 3) :=
  !![2,0,0,1,1,2,2;
     0,0,0,1,1,0,0;
     0,1,2,1,2,1,2;
     1,1,2,1,1,0,2;
     2,1,2,1,0,0,1;
     2,2,0,0,2,0,0;
     2,2,0,0,2,1,1]

def basisInverse : Mat (ZMod 3) :=
  !![2,1,0,0,0,1,2;
     2,1,1,0,2,1,1;
     1,0,0,1,1,1,1;
     1,0,1,0,2,0,0;
     2,1,2,0,1,0,0;
     0,0,2,2,2,1,2;
     0,0,1,1,1,1,2]

theorem basisMatrix_mul_inverse : basisMatrix * basisInverse = 1 := by decide

theorem basisInverse_mul_matrix : basisInverse * basisMatrix = 1 := by decide

/-- The change of basis is an actual invertible matrix. -/
def basisChange : Ambient (ZMod 3) :=
  ⟨basisMatrix, basisInverse, basisMatrix_mul_inverse, basisInverse_mul_matrix⟩

/-- The marked three-cycle permutation gives the literal Ree root matrix. -/
theorem gamma_intertwine :
    gammaMatrix (F := ZMod 3) 0 1 * basisMatrix = basisMatrix * deletedMatrix gammaPerm := by
  simp only [gammaMatrix, map_one, one_pow]
  decide

/-- The marked involution gives the literal Ree Weyl matrix. -/
theorem weyl_intertwine :
    upsilonMatrix (F := ZMod 3) * basisMatrix = basisMatrix * deletedMatrix weylPerm := by decide

end Atlas.ReeG2.TernaryDerived
