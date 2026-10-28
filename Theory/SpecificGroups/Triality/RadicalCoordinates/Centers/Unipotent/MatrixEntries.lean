module

public import Theory.SpecificGroups.Triality.PositiveRootCoordinates

/-!
# The first arm coordinate of a positive Geck element

The Cartan/opposite-arm entry of the ordered positive product is its first
parameter. The existing root-height filtration proves that higher products
cannot contribute to this entry. Commutation with the central simple curve
at parameter one forces that entry to vanish, by one row and one column of
the full 28-dimensional Geck matrices. No field-size restriction is used.

Source: the root parametrizations in GLS3 §§2.4 and 2.6
(`refs/KGroup/GLS3/chapter2.tex`), used in Aschbacher–Smith F.1.12(4).
-/

@[expose] public section

open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.PositiveCoordinates
open Triality.Standard.PositiveCoordinates.SumExchangeData
open RootPairing.IntegralGeckConstruction
open Triality.Standard.Parabolics.RankOneMatrices
namespace Triality.Standard.RadicalCoordinates.Centers.UnipotentMatrices
noncomputable section
local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

def matrixHom (P : Parameters) : SplitGroup P →* Matrix Index Index (ExtensionField P) :=
  (Matrix.reindexRingEquiv (ExtensionField P) latticeEnumeration.symm).toMonoidHom.comp
    ((Units.coeHom _).comp (RootPairing.SimpleGeckGroup.subgroup
      (typeDRootPairing_base 2) (ExtensionField P)).subtype)

lemma matrixHom_curve (P : Parameters) (hp : P.prime = 2)
    (i : Fin 12) (t : ExtensionField P) :
    let : CharP (ExtensionField P) 2 := hp ▸ inferInstance
    matrixHom P (curve P i t) = matrixCurve (positiveIndex i) t := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstance
  exact rootCurve_matrix_of_coefficients canonicalCoefficient_eq i t

lemma matrixHom_injective (P : Parameters) : Function.Injective (matrixHom P) := by
  intro x y h
  apply Subtype.ext
  apply Units.ext
  exact (Matrix.reindexRingEquiv (ExtensionField P) latticeEnumeration.symm).injective h

private def rootHeight : typeDRootSpan 4 →+ ℝ where
  toFun x := 3 * x.val 0 + 2 * x.val 1 + x.val 2
  map_zero' := by simp
  map_add' x y := by simp only [Submodule.coe_add, Pi.add_apply]; ring

private lemma rootHeight_rootIndex (i : Fin 12) :
    rootHeight ((typeDRootPairing 2).root (rootIndex i)) =
      ![1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 5] i := by
  fin_cases i <;>
    norm_num [rootHeight, rootIndex, difference, sumRoot,
      typeDRootPairing_root_val, typeDRootEmbedding, typeDRootVector,
      basisVector, Pi.single_apply, Fin.ext_iff]

variable {F : Type*} [CommRing F] [CharP F 2]

private lemma product_arm_entry (P : Parameters) (hp : P.prime = 2) (v : Coordinates P) :
    matrixHom P (orderedProduct P v) (.inl 0) (.inr 2) = v 0 := by
  let d := fun j => rootHeight (Injectivity.rootWeight (b := typeDRootPairing_base 2) j)
  let c : LatticeIndex := .inl (typeDRootPairing_baseEquiv 2 0)
  let r : LatticeIndex := .inr (rootEnumeration 2)
  let A (i : Fin 12) := (curve P i (v i)).val.val
  have hraise (i : Fin 12) : Injectivity.Raises d 1 (A i - 1) := by
    have hpos : 1 ≤ rootHeight ((typeDRootPairing 2).root (rootIndex i)) := by
      rw [rootHeight_rootIndex]; fin_cases i <;> norm_num
    exact (Injectivity.rootMatrix_raises rootHeight (rootIndex i) (rootIndex_positive i)
      (by linarith) (v i)).mono d hpos
  have he := Injectivity.prod_entry_eq_sum d 1 (by norm_num)
    (List.ofFn A) (by intro B hB; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hB; exact hraise i)
    c r (by
      simp only [d, c, r, Injectivity.rootWeight, Sum.elim_inl, Sum.elim_inr, map_zero]
      change 0 ≤ 1 + (3 * (((typeDRootPairing 2).root (rootEnumeration 2) : Vec 4) 0) +
        2 * (((typeDRootPairing 2).root (rootEnumeration 2) : Vec 4) 1) +
        (((typeDRootPairing 2).root (rootEnumeration 2) : Vec 4) 2))
      simp only [rootCoords_spec]
      rw [show rootCoords 2 0 = -1 from rfl, show rootCoords 2 1 = 1 from rfl,
        show rootCoords 2 2 = 0 from rfl]
      norm_num)
  have hentry (i : Fin 12) (hi : i ≠ 0) : (A i - 1) c r = 0 := by
    have hn : rootIndex i ≠ rootIndex 0 := rootIndex_injective.ne hi
    have hz := Injectivity.rootMatrix_other_cartan rootHeight (rootIndex 0) (rootIndex i)
      (rootIndex_positive i) (by rw [rootHeight_rootIndex]; norm_num)
      (by rw [rootHeight_rootIndex, rootHeight_rootIndex]; fin_cases i <;> norm_num)
      hn (v i) (typeDRootPairing_baseEquiv 2 0)
    have hr : (typeDRootPairing 2).reflectionPerm (rootIndex 0) (rootIndex 0) =
        rootEnumeration 2 := by
      exact (rootEnumeration_reflectionTable 0 1).symm
    rw [hr] at hz
    change (Injectivity.rootMatrix (b := typeDRootPairing_base 2) (rootIndex i) (v i) - 1)
      (.inl (typeDRootPairing_baseEquiv 2 0)) (.inr (rootEnumeration 2)) = 0
    simpa only [Matrix.sub_apply, Matrix.one_apply, Sum.inl_ne_inr, if_false, sub_zero] using hz
  have hsum : (((List.ofFn A).map (fun B => B - 1)).sum : Matrix LatticeIndex LatticeIndex (ExtensionField P)) c r = (A 0 - 1) c r := by
    rw [List.map_ofFn]
    change (∑ i : Fin 12, (A i - 1)) c r = _
    simp only [Matrix.sum_apply]
    exact Finset.sum_eq_single 0 (fun i _ hi => hentry i hi) (by simp)
  rw [hsum] at he
  have hprod : matrixHom P (orderedProduct P v) (.inl 0) (.inr 2) =
      (List.ofFn A).prod c r := by
    change ((Units.coeHom _).comp (RootPairing.SimpleGeckGroup.subgroup
      (typeDRootPairing_base 2) (ExtensionField P)).subtype) (orderedProduct P v) c r = _
    simp only [orderedProduct, map_list_prod, List.map_ofFn]
    rfl
  rw [hprod, he]
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstance
  have hfirst := congrFun₂ (matrixHom_curve P hp 0 (v 0)) (.inl 0) (.inr 2)
  have hc : (A 0) c r = v 0 := by
    change matrixHom P (curve P 0 (v 0)) (.inl 0) (.inr 2) = _
    rw [hfirst]
    norm_num [matrixCurve, positiveIndex, linearCoefficient, quadraticCoefficient,
      negativeIndex, simpleCoefficients, Matrix.one_apply, scalarMap, Sum.inl_ne_inr]
  simp only [Matrix.sub_apply, hc]
  abel

private lemma central_row_check (r : Index) :
    linearCoefficient 13 (.inl 0) r = 0 ∧ quadraticCoefficient 13 (.inl 0) r = 0 := by
  revert r
  decide +kernel

private lemma central_column_check (r : Index) :
    linearCoefficient 13 r (.inr 6) = (if r = .inr 2 then 1 else 0) ∧
    quadraticCoefficient 13 r (.inr 6) = 0 := by
  revert r
  decide +kernel

private lemma commuting_arm_entry (A : Matrix Index Index F)
    (h : Commute A (matrixCurve 13 (1 : F))) : A (.inl 0) (.inr 2) = 0 := by
  have hr (r : Index) : matrixCurve 13 (1 : F) (.inl 0) r =
      (1 : Matrix Index Index F) (.inl 0) r := by
    obtain ⟨hl, hq⟩ := central_row_check r
    simp [matrixCurve, RingHom.mapMatrix_apply, hl, hq]
  have hc (r : Index) : matrixCurve 13 (1 : F) r (.inr 6) =
      (1 : Matrix Index Index F) r (.inr 6) + if r = .inr 2 then 1 else 0 := by
    obtain ⟨hl, hq⟩ := central_column_check r
    simp [matrixCurve, RingHom.mapMatrix_apply, hl, hq]
  have he := congrFun₂ h.eq (.inl 0) (.inr 6)
  simp only [Matrix.mul_apply, hr, hc, mul_add, Finset.sum_add_distrib] at he
  simp only [← Matrix.mul_apply, mul_one, one_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at he
  exact (add_eq_left.mp he)

lemma first_coordinate_zero (P : Parameters) (hp : P.prime = 2) (v : Coordinates P)
    (h : Commute (orderedProduct P v) (curve P 3 1)) : v 0 = 0 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstance
  have he := h.map (matrixHom P)
  rw [matrixHom_curve P hp] at he
  exact (product_arm_entry P hp v).symm.trans (commuting_arm_entry _ he)

end
end Triality.Standard.RadicalCoordinates.Centers.UnipotentMatrices
