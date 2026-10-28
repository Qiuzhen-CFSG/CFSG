module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.Subgroup
public import Mathlib.Data.Matrix.Mul

/-!
# A vector orbit for the J₄ coset problem

The subgroup program in `Cardinality.Subgroup` suggests using the orbit of a
fixed row vector in the ATLAS 112-dimensional representation. We specify that
vector in the source basis, with bit `j` giving coordinate `j`.

This module defines its actual matrix orbit and stabilizer, and proves the
fiber criterion for right cosets. It does not assert the size of the orbit or
identify the stabilizer with the subgroup from the program. Those are separate
concrete certification obligations.

Source representation: https://brauer.maths.qmul.ac.uk/Atlas/v3/matrep/J4G1-f2r112B0 .
-/

@[expose] public section
namespace Janko4.Cardinality

abbrev CosetVector := Fin 112 → ZMod 2

/-- Candidate base vector in the unchanged ATLAS row-coordinate convention. -/
def cosetBaseVector : CosetVector :=
  fun j => if (1383886125678978288045195946262397 : ℕ).testBit j.val then 1 else 0

/-- Right multiplication of a row vector by an actual matrix of the model. -/
def vectorRight (v : CosetVector) (g : Model) : CosetVector :=
  Matrix.vecMul v (toMatrix g)

@[simp] theorem vectorRight_one (v : CosetVector) : vectorRight v 1 = v := by
  simp [vectorRight]

theorem vectorRight_mul (v : CosetVector) (g h : Model) :
    vectorRight v (g * h) = vectorRight (vectorRight v g) h := by
  simp only [vectorRight, map_mul, Matrix.vecMul_vecMul]

/-- The matrix image of the base vector. -/
def cosetOrbitMap (g : Model) : CosetVector := vectorRight cosetBaseVector g

@[simp] theorem cosetOrbitMap_one : cosetOrbitMap 1 = cosetBaseVector :=
  vectorRight_one _

/-- The orbit as a subtype of actual binary vectors, not an abstract table. -/
def CosetVectorOrbit := Set.range cosetOrbitMap

instance cosetVectorOrbitFinite : Finite CosetVectorOrbit :=
  inferInstanceAs (Finite ↥(Set.range cosetOrbitMap))

/-- The stabilizer for right multiplication in the concrete matrix carrier. -/
def cosetVectorStabilizer : Subgroup Model where
  carrier := {g | cosetOrbitMap g = cosetBaseVector}
  one_mem' := cosetOrbitMap_one
  mul_mem' := by
    intro g h hg hh
    change vectorRight cosetBaseVector (g * h) = cosetBaseVector
    rw [vectorRight_mul, show vectorRight cosetBaseVector g = cosetBaseVector from hg]
    exact hh
  inv_mem' := by
    intro g hg
    change vectorRight cosetBaseVector g⁻¹ = cosetBaseVector
    change cosetOrbitMap g = cosetBaseVector at hg
    have he := congrArg (fun v => vectorRight v g⁻¹) hg
    simpa only [cosetOrbitMap, ← vectorRight_mul, mul_inv_cancel, vectorRight_one] using
      he.symm

/-- Equal orbit points are exactly equal right cosets of the vector stabilizer. -/
theorem cosetOrbitMap_eq_iff (g h : Model) :
    cosetOrbitMap g = cosetOrbitMap h ↔ g * h⁻¹ ∈ cosetVectorStabilizer := by
  change vectorRight cosetBaseVector g = vectorRight cosetBaseVector h ↔
    vectorRight cosetBaseVector (g * h⁻¹) = cosetBaseVector
  constructor
  · intro he
    rw [vectorRight_mul, he, ← vectorRight_mul, mul_inv_cancel, vectorRight_one]
  · intro he
    have hh := congrArg (fun v => vectorRight v h) he
    simpa only [← vectorRight_mul, inv_mul_cancel_right] using hh

/-- The quotient projection, with its range made explicit. -/
def cosetOrbitPoint (g : Model) : CosetVectorOrbit := ⟨cosetOrbitMap g, g, rfl⟩

theorem cosetOrbitPoint_surjective : Function.Surjective cosetOrbitPoint := by
  rintro ⟨v, g, rfl⟩
  exact ⟨g, rfl⟩

end Janko4.Cardinality
