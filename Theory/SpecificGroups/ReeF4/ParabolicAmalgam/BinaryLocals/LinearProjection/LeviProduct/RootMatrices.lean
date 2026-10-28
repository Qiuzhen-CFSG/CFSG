module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection.Levi
public import Theory.AlgebraicGroup.RootSystems.IntegralRootCurveSimpleGeneration
public import Theory.AlgebraicGroup.RootSystems.SimpleGeckGroup.Commutation
public import Mathlib.Algebra.CharP.Two

/-!
# Binary F₄ rank-one matrix relations

The actual signed simple-root curves agree with the integral Geck curves.
Their additive laws give involutions over the binary field; specializing the
integral Tits exchange identity gives the length-three braid relation. A
Cartan-column entry distinguishes the two generators at node 0.

Source: the integral Chevalley construction of Steinberg and Geck; the end-node
A₁ × A₁ Levi used in Aschbacher–Smith F.1.12(I)(5), printed pp.263–264 of
`refs/quasithin.pdf`.
-/

@[expose] public section
open scoped Matrix
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
namespace ReeF4.Parabolics.BinaryLinear.LeviProductProof
noncomputable section
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

abbrev node (i : Fin 4) := typeF4RootPairing_baseEquiv i

def pos (i : Fin 4) : SplitGroup 0 := rootGeneratorInGroup 0 (typeF4SimpleRootIndex i) 1
def neg (i : Fin 4) : SplitGroup 0 := rootGeneratorInGroup 0 (-typeF4SimpleRootIndex i) 1

lemma pos_coe (i : Fin 4) : (pos i).val = positiveUnit (node i) (1 : CoefficientField 0) := by
  simp only [pos, rootGeneratorInGroup_coe, F4Chevalley.rootCurve,
    F4Chevalley.integralOperators, ← typeF4RootPairing_baseEquiv_val, rootCurveUnit_simple]

lemma neg_coe (i : Fin 4) : (neg i).val = negativeUnit (node i) (1 : CoefficientField 0) := by
  simp only [neg, rootGeneratorInGroup_coe, F4Chevalley.rootCurve,
    F4Chevalley.integralOperators, ← typeF4RootPairing_baseEquiv_val, rootCurveUnit_neg_simple]

lemma pos_sq (i : Fin 4) : pos i * pos i = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, pos_coe, ← positiveUnit_add]
  change positiveUnit (node i) ((1 : CoefficientField 0) + 1) = 1
  apply Units.ext
  simp [positiveUnit_val, CharTwo.add_self_eq_zero]

lemma neg_sq (i : Fin 4) : neg i * neg i = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, neg_coe, ← negativeUnit_add]
  change negativeUnit (node i) ((1 : CoefficientField 0) + 1) = 1
  apply Units.ext
  simp [negativeUnit_val, CharTwo.add_self_eq_zero]

private lemma map_e (i : typeF4RootPairing_base.support) (t : ℤ) :
    (eUnipotent i t).map (Int.castRingHom (CoefficientField 0)) =
      positiveMatrix i (t : CoefficientField 0) := by
  ext x y
  simp only [eUnipotent, positiveMatrix_formula, Matrix.map_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  simp [Matrix.one_apply]

private lemma map_f (i : typeF4RootPairing_base.support) (t : ℤ) :
    (fUnipotent i t).map (Int.castRingHom (CoefficientField 0)) =
      negativeMatrix i (t : CoefficientField 0) := by
  ext x y
  simp only [fUnipotent, negativeMatrix_formula, Matrix.map_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  simp [Matrix.one_apply]

lemma pos_neg_braid (i : Fin 4) : pos i * neg i * pos i = neg i * pos i * neg i := by
  have h : (pos i * neg i * pos i) * pos i = neg i * (pos i * neg i * pos i) := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, pos_coe, neg_coe, Units.val_mul, positiveUnit_val, negativeUnit_val]
    have he := congrArg (Matrix.map · (Int.castRingHom (CoefficientField 0)))
      (titsLift_mul_eUnipotent (node i) 1)
    simpa only [titsLift, Matrix.map_mul, map_e, map_f, Int.cast_one, Int.cast_neg,
      CharTwo.neg_eq] using he
  have he := congrArg (· * pos i) h
  simpa only [mul_assoc, pos_sq, mul_one] using he

private lemma e_entry : eUnipotent (node 0) 1
    (.inr ((node 0 : typeF4RootPairing_base.support) : F4Chevalley.Root)) (.inl (node 1)) = 1 := by
  have hc : typeF4RootPairing_base.cartanMatrix (node 0) (node 1) = -1 := by
    rw [typeF4RootPairing_base_cartan_apply]
    rfl
  have h := congrFun (eUnipotent_mulVec_u (node 0) (node 1) 1)
    (.inr ((node 0 : typeF4RootPairing_base.support) : F4Chevalley.Root))
  simpa [u, v, Matrix.mulVec_single_one, Pi.single_apply, hc] using h

private lemma f_entry : fUnipotent (node 0) 1
    (.inr ((node 0 : typeF4RootPairing_base.support) : F4Chevalley.Root)) (.inl (node 1)) = 0 := by
  have hc : typeF4RootPairing_base.cartanMatrix (node 0) (node 1) = -1 := by
    rw [typeF4RootPairing_base_cartan_apply]
    rfl
  have hn : typeF4SimpleRootIndex 0 ≠
      typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 0) (typeF4SimpleRootIndex 0) :=
    typeF4RootPairing.ne_neg (typeF4SimpleRootIndex 0)
  have h := congrFun (fUnipotent_mulVec_u (node 0) (node 1) 1)
    (.inr ((node 0 : typeF4RootPairing_base.support) : F4Chevalley.Root))
  change (fUnipotent (node 0) 1 *ᵥ u (node 1)) (.inr ((node 0).val)) =
    (u (node 1) + 1 • (|typeF4RootPairing_base.cartanMatrix (node 0) (node 1)| •
      v (b := typeF4RootPairing_base) (-(node 0).val))) (.inr ((node 0).val)) at h
  simpa [u, v, Matrix.mulVec_single_one, Pi.single_apply, hc, hn] using h

lemma pos_neg_ne : pos 0 ≠ neg 0 := by
  intro he
  have h := congrArg (fun x : SplitGroup 0 => x.val.val
    (.inr (node 0).val) (.inl (node 1))) he
  rw [pos_coe, neg_coe] at h
  change positiveMatrix (node 0) ((1 : ℤ) : CoefficientField 0) _ _ =
    negativeMatrix (node 0) ((1 : ℤ) : CoefficientField 0) _ _ at h
  rw [← map_e, ← map_f, Matrix.map_apply, Matrix.map_apply, e_entry, f_entry] at h
  exact one_ne_zero (by simpa only [map_one, map_zero] using h)

lemma twist_pos (i : Fin 4) : reeTwist 0 (pos i) = pos (Fin.revPerm i) := by
  simp only [pos, reeTwist_root_zero, exceptionalRootPermutation_simple]
lemma twist_neg (i : Fin 4) : reeTwist 0 (neg i) = neg (Fin.revPerm i) := by
  simp only [neg, reeTwist_root_zero, exceptionalRootPermutation_neg_simple]

private lemma node_ne : node 0 ≠ node 3 := by
  intro h
  have := typeF4RootPairing_baseEquiv.injective h
  exact (by decide : (0 : Fin 4) ≠ 3) this
private lemma cartan_zero : typeF4RootPairing_base.cartanMatrix (node 3) (node 0) = 0 := by
  rw [typeF4RootPairing_base_cartan_apply]
  rfl

lemma commute_pos_pos : Commute (pos 0) (pos 3) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, pos_coe]
  exact congrArg Subtype.val
    (commute_positive_positive_of_cartan_eq_zero (node 0) (node 3) node_ne cartan_zero
      (1 : CoefficientField 0) 1).eq
lemma commute_pos_neg : Commute (pos 0) (neg 3) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, pos_coe, neg_coe]
  exact congrArg Subtype.val
    (commute_positive_negative (node 0) (node 3) node_ne (1 : CoefficientField 0) 1).eq
lemma commute_neg_pos : Commute (neg 0) (pos 3) := by
  apply Commute.symm
  apply Subtype.ext
  simp only [Subgroup.coe_mul, pos_coe, neg_coe]
  exact congrArg Subtype.val
    (commute_positive_negative (node 3) (node 0) node_ne.symm (1 : CoefficientField 0) 1).eq
lemma commute_neg_neg : Commute (neg 0) (neg 3) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, neg_coe]
  exact congrArg Subtype.val
    (commute_negative_negative_of_cartan_eq_zero (node 0) (node 3) node_ne cartan_zero
      (1 : CoefficientField 0) 1).eq
end
end ReeF4.Parabolics.BinaryLinear.LeviProductProof
