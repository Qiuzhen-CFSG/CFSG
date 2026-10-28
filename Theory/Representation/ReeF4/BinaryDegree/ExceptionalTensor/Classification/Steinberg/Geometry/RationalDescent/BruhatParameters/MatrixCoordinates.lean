module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters.TorusRecovery
public import Mathlib.Algebra.Field.Subfield.Basic

/-!
# The faithful matrix coordinates used in Bruhat recovery

The inverse of the concrete matrix-to-ambient equivalence sends carrier
points to their literal Geck matrices. Their entries are presented variety
coordinates after the fixed basis reindexing. This connects triangular
matrix extraction to rationality of the actual carrier point.

Source: the matrix calculation in Steinberg's Theorem 7, pp. 64–65 of
`refs/KGroup/GLS3/Chapter2St1.tex`.
-/

@[expose] public noncomputable section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters

universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

def pointMatrix : Variety.Point (F4Chevalley.Carrier (k := F)) →*
    (Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F)ˣ :=
  F4Chevalley.matrixAmbientEquiv.symm.toMonoidHom.comp
    (F4Chevalley.ambientClosedCarrier (k := F)).inclusion.onPoints

theorem pointMatrix_injective : Function.Injective (pointMatrix (F := F)) :=
  F4Chevalley.matrixAmbientEquiv.symm.injective.comp
    (F4Chevalley.ambientClosedCarrier (k := F)).inclusion_injective

theorem pointMatrix_ambient (x : Variety.Point (F4Chevalley.Carrier (k := F))) :
    F4Chevalley.matrixToAmbient (pointMatrix x) =
      (F4Chevalley.ambientClosedCarrier (k := F)).inclusion.onPoints x :=
  F4Chevalley.matrixAmbientEquiv.apply_symm_apply _

theorem pointMatrix_root (r : F4Chevalley.Root) (a : F) :
    pointMatrix (algebraicRootElement r a) = F4Chevalley.rootCurve r a := by
  apply F4Chevalley.matrixToAmbient_bijective.1
  rw [pointMatrix_ambient, algebraicRootElement, F4Chevalley.rootMorphism_inclusion_apply,
    F4Chevalley.matrixToAmbient_root]

theorem pointMatrix_corootProduct (t : Fin 4 → Fˣ) :
    pointMatrix (corootProduct t) = F4Chevalley.torusElement t⁻¹ := by
  apply F4Chevalley.matrixToAmbient_bijective.1
  rw [pointMatrix_ambient, corootProduct_ambient]

/-- Equality with the presented coordinate, not merely an unspecified faithful
representation. -/
theorem pointMatrix_coordinate (x : Variety.Point (F4Chevalley.Carrier (k := F)))
    (i j : F4Chevalley.BasisIndex) :
    (pointMatrix x).val i j = x.val (Sum.inl
      (F4Chevalley.carrierIndexEquiv (k := F) i,
       F4Chevalley.carrierIndexEquiv (k := F) j)) := by
  have h := congrArg (fun y : Variety.Point (F4Chevalley.Ambient F) =>
    y.val (Sum.inl (F4Chevalley.carrierIndexEquiv (k := F) i,
      F4Chevalley.carrierIndexEquiv (k := F) j))) (pointMatrix_ambient x)
  change _ = ((F4Chevalley.ambientClosedCarrier (k := F)).pointEquiv x).val.val _ at h
  rw [ClosedSubgroup.pointEquiv_val] at h
  change (generalLinearRepresentationPoint F4Chevalley.carrierBasis
    (Matrix.GeneralLinearGroup.toLin (pointMatrix x))).val _ = x.val _ at h
  rw [generalLinearRepresentationPoint_matrix] at h
  simpa [F4Chevalley.carrierBasis, carrierBasis, Module.Basis.reindex_apply] using h

omit [IsAlgClosed F] in
private theorem entries_mul (S : Subfield F)
    (A B : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F)
    (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S) :
    ∀ i j, (A * B) i j ∈ S := by
  intro i j
  exact S.sum_mem fun k _ => S.mul_mem (hA i k) (hB k j)

omit [IsAlgClosed F] in
private theorem rootCurve_entries (S : Subfield F) (r : F4Chevalley.Root)
    (a : F) (ha : a ∈ S) : ∀ i j, (F4Chevalley.rootCurve r a).val i j ∈ S := by
  classical
  intro i j
  have h1 : (1 : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F) i j ∈ S := by
    simp only [Matrix.one_apply]
    split_ifs <;> first | exact S.one_mem | exact S.zero_mem
  have hint (A : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex ℤ) :
      specializeMatrix (S := F) A i j ∈ S := S.intCast_mem _
  rw [F4Chevalley.rootCurve_matrix_formula]
  exact S.add_mem (S.add_mem (S.add_mem h1 (S.mul_mem ha (hint _)))
    (S.mul_mem (S.pow_mem ha 2) (hint _))) (S.mul_mem (S.pow_mem ha 3) (hint _))

/-- Every inverse Weyl word is defined over every subfield: it is still a
finite product of actual root matrices with parameters `1` and `-1`. -/
theorem weylWord_inv_entries (S : Subfield F) (l : List (Fin 4)) :
    ∀ i j, (pointMatrix ((weylWord (F := F) l)⁻¹)).val i j ∈ S := by
  have hn (r : F4Chevalley.Root) :
      ∀ i j, (pointMatrix ((algebraicNElement r (1 : Fˣ))⁻¹)).val i j ∈ S := by
    simp only [map_inv, algebraicNElement, map_mul, pointMatrix_root, Units.val_one,
      inv_one, mul_inv_rev, F4Chevalley.rootCurve_inv, neg_neg, Units.val_mul]
    exact entries_mul S _ _ (rootCurve_entries S _ _ (S.neg_mem S.one_mem))
      (entries_mul S _ _ (rootCurve_entries S _ _ S.one_mem)
        (rootCurve_entries S _ _ (S.neg_mem S.one_mem)))
  induction l with
  | nil =>
    intro i j
    simp only [weylWord, List.map_nil, List.prod_nil, inv_one, map_one, Units.val_one,
      Matrix.one_apply]
    split_ifs <;> first | exact S.one_mem | exact S.zero_mem
  | cons r l ih =>
    change ∀ i j, (pointMatrix
      ((algebraicNElement (typeF4SimpleRootIndex r) 1 * weylWord l)⁻¹)).val i j ∈ S
    rw [mul_inv_rev, map_mul, Units.val_mul]
    exact entries_mul S _ _ ih (hn _)

/-- Removing the explicit Weyl factor preserves rational matrix entries. -/
theorem right_weyl_inv_entries_mem_range {K : Type*} [Field K] (f : K →+* F)
    (x : Variety.Point (F4Chevalley.Carrier (k := F))) (l : List (Fin 4))
    (hx : ∀ c, x.val c ∈ f.range) :
    ∀ i j, (pointMatrix (x * (weylWord l)⁻¹)).val i j ∈ f.range := by
  have h := entries_mul f.fieldRange (pointMatrix x).val
    (pointMatrix ((weylWord l)⁻¹)).val
    (fun i j => by rw [pointMatrix_coordinate]; exact hx _)
    (weylWord_inv_entries f.fieldRange l)
  simpa only [map_mul, Units.val_mul, RingHom.mem_fieldRange, RingHom.mem_range] using h

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters
