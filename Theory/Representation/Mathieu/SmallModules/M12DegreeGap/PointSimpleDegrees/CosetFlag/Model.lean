module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.Interface
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.Witness

/-!
# Concrete certificate boundaries for the M₁₁ eleven-coset flag

The matrices below decode the published 720-column witnesses. The permutation
matrix uses the forward left-coset action: column j is the image of the delta
function at coset j. Thus its action on functions is the inverse permutation.
The native-coset comparison and the binary matrix identities are independent
finite obligations. `Construction` uses both to construct the actual invariant
subspaces and coordinates on their literal successive quotients.

Source: James, *The modular characters of the Mathieu groups*, J. Algebra 27
(1973), 57–111; witness conventions in `../source/README.md`.
-/

@[expose] public section
namespace Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.CosetFlag
open Data

abbrev Space := Fin 720 → ZMod 2

def bit (a r : ℕ) : ZMod 2 := if a.testBit r then 1 else 0

def basisMatrix : Matrix (Fin 720) (Fin 720) (ZMod 2) :=
  fun r c => bit Witness.basisColumns[c.val]! r.val

def inverseMatrix : Matrix (Fin 720) (Fin 720) (ZMod 2) :=
  fun r c => bit Witness.inverseColumns[c.val]! r.val

def actionMatrix (s : Fin 2) : Matrix (Fin 720) (Fin 720) (ZMod 2) :=
  fun r c => bit (Witness.adaptedColumns[s.val]!)[c.val]! r.val

def cosetMatrix (s : Fin 2) : Matrix (Fin 720) (Fin 720) (ZMod 2) :=
  fun r c => if r = (Witness.leftAction[s.val]!)[c.val]! then 1 else 0

/-- Endpoints are clamped after the final stage. -/
def cut (m : ℕ) : ℕ := Witness.endpoints[min m 33]!

theorem cut_zero : cut 0 = 0 := by decide +kernel

theorem cut_last : cut 33 = 720 := by decide +kernel

theorem cut_eq_full (m : ℕ) (hm : 33 ≤ m) : cut m = 720 := by
  simp only [cut, Nat.min_eq_right hm]
  rfl

theorem cut_step (t : Factor) :
    cut t.val + degree t = cut (t.val + 1) ∧ cut (t.val + 1) ≤ 720 := by
  revert t
  decide +kernel

def blockIndex (t : Factor) (x : Fin (degree t)) : Fin 720 :=
  ⟨cut t.val + x.val, by have h := cut_step t; omega⟩

/-- Coordinates of the actual coset module, retaining the native A/B actions.
No identification with an abstract free-group representation suffices here. -/
structure CosetCoordinates where
  coordinates : (ElevenCoset → ZMod 2) ≃ₗ[ZMod 2] Space
  generator_coordinates : ∀ (s : Fin 2) v,
    coordinates (cosetRepresentation (generator s) v) =
      (cosetMatrix s).mulVec (coordinates v)

/-- Concrete identities for the published basis and adapted matrices.
This record is an obligation, not an assertion that the witnesses satisfy it. -/
structure MatrixIdentities : Prop where
  inverse : inverseMatrix * basisMatrix = 1
  action : ∀ s : Fin 2, cosetMatrix s * basisMatrix = basisMatrix * actionMatrix s
  upper : ∀ (t : Factor) (s : Fin 2) (x y : Fin 720),
    cut t.val ≤ x.val → y.val < cut t.val → actionMatrix s x y = 0
  diagonal : ∀ (t : Factor) (s : Fin 2) (x y : Fin (degree t)),
    actionMatrix s (blockIndex t x) (blockIndex t y) = factorMatrix t s x y

end Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.CosetFlag
