module

public import Theory.Representation.SL3FourNaturalDual.CentralSections
public import Theory.Representation.FirstCohomologyLinearTransport
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# The two mixed nine-dimensional SL₃(4) tensor models

These are the actual coordinate actions dual(g) tensor Frobenius(g), and
natural(g) tensor Frobenius(dual(g)). Coordinates (i,k) have index 3*i+k.
The binary restrictions have central scalars omega and omega squared,
respectively. These definitions assert no recognition or degree catalogue.

The model formulas expose their bodies for the finite extension certificates
and for the separate tensor-coordinate and field-descent comparison.
Source context: GLS III, 2.8.6 and 2.8.10(c), and Guralnick–Malle,
Classification of 2F-modules I, Proposition 5.1, pp.15–16.
-/

@[expose] public noncomputable section
open Matrix
open scoped Kronecker
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsNine.Simple
open Representation.SL3FourNaturalDual
abbrev Matrix9 := Matrix (Fin 9) (Fin 9) F
abbrev Space9 := Fin 9 → F
/-- The untwisted natural or inverse-transpose factor. -/
def firstFactorMatrix (b : Bool) : SL →* Matrix (Fin 3) (Fin 3) F :=
  if b then SpecialLinearGroup.coeMonoidHom else
    SpecialLinearGroup.coeMonoidHom.comp SpecialLinearGroup.inverseTranspose
/-- The opposite factor, with every coefficient squared. -/
def secondFactorMatrix (b : Bool) : SL →* Matrix (Fin 3) (Fin 3) F :=
  (frobenius F 2).mapMatrix.toMonoidHom.comp (firstFactorMatrix (!b))
/-- The tensor matrix in the specified nine coordinates. -/
def mixedMatrix (b : Bool) : SL →* Matrix9 :=
  (Matrix.reindexRingEquiv F finProdFinEquiv).toMonoidHom.comp {
    toFun g := firstFactorMatrix b g ⊗ₖ secondFactorMatrix b g
    map_one' := by rw [map_one, map_one, Matrix.one_kronecker_one]
    map_mul' g h := by rw [map_mul, map_mul, Matrix.mul_kronecker_mul] }
/-- The tensor action over the actual four-element field. -/
def mixedFieldRep (b : Bool) : Representation F SL Space9 :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp (mixedMatrix b)
/-- The same operators regarded as binary linear maps. -/
def mixedBinaryRep (b : Bool) : Representation (ZMod 2) SL Space9 :=
  Representation.restrictScalars (k := ZMod 2) (mixedFieldRep b)
lemma mixedMatrix_apply (b : Bool) (g : SL) (r c : Fin 9) :
    mixedMatrix b g r c =
      firstFactorMatrix b g ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm r).1 ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm c).1 *
      secondFactorMatrix b g ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm r).2 ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm c).2 := rfl

/-- The central character in each orientation. -/
def centralValue : Bool → F :=
  fun b => if b then (QuadraticAlgebra.omega : F) ^ 2 else QuadraticAlgebra.omega
lemma mixedMatrix_central : ∀ b : Bool,
    mixedMatrix b centralScalar = Matrix.diagonal (fun _ => centralValue b) := by
  decide +kernel
lemma mixedBinaryRep_central (b : Bool) (v : Space9) :
    mixedBinaryRep b centralScalar v = centralValue b • v := by
  change (mixedMatrix b centralScalar).mulVec v = _
  rw [mixedMatrix_central]
  exact Matrix.diagonal_const_mulVec _ _
end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsNine.Simple
