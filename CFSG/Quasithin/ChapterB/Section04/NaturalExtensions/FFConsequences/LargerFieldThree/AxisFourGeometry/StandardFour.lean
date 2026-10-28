module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.Transport
/-!
# A four-group with independent shear directions

The two binary coordinate directions in an F-hyperplane give an injective
four-element shear group. Its displacements include two F-independent
vectors. In any conjugate root group all displacements have one common
F-line, so this four-group lies in no root group.

These are the model witnesses used to extract the original source four-group
from the full axis replacement in B.4.9(2).
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.9(1)–(2), printed pp.92–94.
-/

public section
open Representation Representation.BinaryOffender Matrix
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterK.Linear.Natural
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.LargerFieldThree.AxisFourGeometry
variable (F : BinaryField)

private def binaryDisplacement (p : Fin 2 → ZMod 2) : coordinateHyperplane F 3 0 :=
  ⟨![0, algebraMap (ZMod 2) F.Carrier (p 0), algebraMap (ZMod 2) F.Carrier (p 1)], rfl⟩

private lemma binaryDisplacement_zero : binaryDisplacement F 0 = 0 := by
  ext i
  fin_cases i <;> simp [binaryDisplacement]

private lemma binaryDisplacement_add (p q : Fin 2 → ZMod 2) :
    binaryDisplacement F (p + q) = binaryDisplacement F p + binaryDisplacement F q := by
  ext i
  fin_cases i <;> simp [binaryDisplacement]

private lemma binaryDisplacement_injective : Function.Injective (binaryDisplacement F) := by
  intro p q h
  have h' := congrArg Subtype.val h
  funext i
  fin_cases i
  · exact (algebraMap (ZMod 2) F.Carrier).injective (congrFun h' 1)
  · exact (algebraMap (ZMod 2) F.Carrier).injective (congrFun h' 2)

private noncomputable def fourHom : Multiplicative (Fin 2 → ZMod 2) →*
    SpecialLinearGroup (Fin 3) F.Carrier where
  toFun p := shear F 3 0 (binaryDisplacement F p.toAdd)
  map_one' := by change shear F 3 0 (binaryDisplacement F 0) = 1; rw [binaryDisplacement_zero, shear_zero]
  map_mul' p q := by
    change shear F 3 0 (binaryDisplacement F (p.toAdd + q.toAdd)) = _
    rw [binaryDisplacement_add, shear_add]

private lemma fourHom_injective : Function.Injective (fourHom F) := by
  intro p q h
  apply Multiplicative.ext
  exact binaryDisplacement_injective F (shear_injective F 3 0 h)

/-- The binary plane of the two independent coordinate shears. -/
noncomputable def standardFour : Subgroup (SpecialLinearGroup (Fin 3) F.Carrier) :=
  (fourHom F).range

lemma standardFour_le : standardFour F ≤ hyperplaneCentralizer F 3 0 := by
  rintro _ ⟨p, rfl⟩
  exact shear_mem F 3 0 _

lemma standardFour_card : Nat.card (standardFour F) = 4 := by
  change Nat.card (fourHom F).range = 4
  rw [← Nat.card_congr (MonoidHom.ofInjective (fourHom_injective F)).toEquiv]
  change Nat.card (Fin 2 → ZMod 2) = 4
  norm_num [Nat.card_eq_fintype_card]

lemma standardFour_elementary : IsElementaryAbelian 2 (standardFour F) := by
  refine {
    toIsMulCommutative := ⟨⟨?_⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  · rintro ⟨_, p, rfl⟩ ⟨_, q, rfl⟩
    apply Subtype.ext
    change fourHom F p * fourHom F q = fourHom F q * fourHom F p
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro ⟨_, p, rfl⟩
    apply Subtype.ext
    change fourHom F p ^ 2 = 1
    rw [← map_pow]
    have hp : p ^ 2 = 1 := by
      rw [pow_two]
      apply Multiplicative.ext
      change p.toAdd + p.toAdd = 0
      ext i
      exact CharTwo.add_self_eq_zero _
    rw [hp, map_one]

/-- Root containment on the model uses conjugates by SL₃, not GL₃. -/
@[expose] def InModelRootGroup (A : Subgroup (SpecialLinearGroup (Fin 3) F.Carrier)) : Prop :=
  ∃ s : SpecialLinearGroup (Fin 3) F.Carrier,
    ∃ i j : Fin 3, ∃ hij : i ≠ j, ∀ a ∈ A, ∃ c : F.Carrier,
      a = s * SpecialLinearGroup.transvection hij c * s⁻¹

private lemma root_displacement (s : SpecialLinearGroup (Fin 3) F.Carrier)
    (i j : Fin 3) (hij : i ≠ j) (c : F.Carrier) (v : Fin 3 → F.Carrier) :
    specialLinearNatural 3 (s * SpecialLinearGroup.transvection hij c * s⁻¹) v - v =
      c • specialLinearNatural 3 s (Pi.single i ((specialLinearNatural 3 s⁻¹ v) j)) := by
  have ht (w : Fin 3 → F.Carrier) :
      specialLinearNatural 3 (SpecialLinearGroup.transvection hij c) w =
        w + c • Pi.single i (w j) := by
    change (Matrix.transvection i j c).mulVec w = _
    rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
    congr 1
    ext k
    by_cases hk : k = i <;> simp [hk, smul_eq_mul]
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ht,
    map_add, map_smul, self_inv_apply, add_sub_cancel_left]

private lemma first_shear_mem :
    shear F 3 0 ⟨Pi.single 1 1, by simp [mem_coordinateHyperplane]⟩ ∈ standardFour F := by
  refine ⟨Multiplicative.ofAdd ![1, 0], ?_⟩
  change shear F 3 0 (binaryDisplacement F ![1, 0]) = _
  congr 1
  ext i
  fin_cases i <;> simp [binaryDisplacement]

private lemma second_shear_mem :
    shear F 3 0 ⟨Pi.single 2 1, by simp [mem_coordinateHyperplane]⟩ ∈ standardFour F := by
  refine ⟨Multiplicative.ofAdd ![0, 1], ?_⟩
  change shear F 3 0 (binaryDisplacement F ![0, 1]) = _
  congr 1
  ext i
  fin_cases i <;> simp [binaryDisplacement]

/-- The two independent displacement directions exclude every root group. -/
lemma standardFour_not_root : ¬ InModelRootGroup F (standardFour F) := by
  rintro ⟨s, i, j, hij, hroot⟩
  obtain ⟨a, ha⟩ := hroot _ (first_shear_mem F)
  obtain ⟨b, hb⟩ := hroot _ (second_shear_mem F)
  let v : Fin 3 → F.Carrier := Pi.single 0 1
  let w := specialLinearNatural 3 s (Pi.single i ((specialLinearNatural 3 s⁻¹ v) j))
  have hfirst : (Pi.single 1 1 : Fin 3 → F.Carrier) = a • w := by
    have h := root_displacement F s i j hij a v
    rw [← ha] at h
    change linearNatural F 3 (shear F 3 0 _) v - v = _ at h
    simpa only [shear_apply, v, Pi.single_eq_same, one_smul, add_sub_cancel_left] using h
  have hsecond : (Pi.single 2 1 : Fin 3 → F.Carrier) = b • w := by
    have h := root_displacement F s i j hij b v
    rw [← hb] at h
    change linearNatural F 3 (shear F 3 0 _) v - v = _ at h
    simpa only [shear_apply, v, Pi.single_eq_same, one_smul, add_sub_cancel_left] using h
  have hab : b • (Pi.single 1 1 : Fin 3 → F.Carrier) = a • Pi.single 2 1 := by
    rw [hfirst, hsecond, smul_smul, smul_smul, mul_comm]
  have hb0 : b = 0 := by simpa using congrFun hab 1
  have hzero := congrFun hsecond 2
  simp [hb0] at hzero

end CFSG.Quasithin.ChapterB.NaturalExtensions.LargerFieldThree.AxisFourGeometry
