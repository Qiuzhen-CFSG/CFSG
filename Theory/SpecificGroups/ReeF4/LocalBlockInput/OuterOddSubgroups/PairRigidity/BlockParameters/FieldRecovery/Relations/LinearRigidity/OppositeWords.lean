module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Relations.Actions
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.TorusCharacters
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport.SimpleConjugation

/-!
# Opposite-root words on the Ree linear block

The two orthogonal end nodes give the literal type VI words. Their
parameter-one Weyl word is the product of the two simple Tits lifts.
The checked simple-reflection action exchanges the signed linear curves.
Conjugating by the diagonal matrix with end-root scales `t` and `theta(t)`
gives the exact inverse-square parameter for every nonzero `t`. The braid
relation follows by cancellation. No rank-one identification is assumed.

Source: GLS3, Table 2.4 type VI and §§2.4–2.5,
`refs/KGroup/GLS3/chapter2.tex`; the integral simple-reflection and torus
identities are the concrete Chevalley relations of GLS3 1.12.1.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup ReeF4.WordRelations
open PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.RankOneTransport
private local instance linearRigidityWordsIndexNeg : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
local notation "s" => typeF4RootPairing_baseEquiv
variable {m : ℕ}

private def X (i : Fin 4) (t : CoefficientField m) :=
  F4Chevalley.rootCurve (typeF4SimpleRootIndex i) t
private def Y (i : Fin 4) (t : CoefficientField m) :=
  F4Chevalley.rootCurve (-typeF4SimpleRootIndex i) t
private def L (p : Bool) (t : CoefficientField m) := (linearWord m p t).val
private def W (t : CoefficientField m) := L true t * L false t⁻¹ * L true t

private theorem X_pos (i : Fin 4) (t : CoefficientField m) : X i t = positiveUnit (s i) t := by
  simp only [X, F4Chevalley.rootCurve, F4Chevalley.integralOperators,
    ← typeF4RootPairing_baseEquiv_val, rootCurveUnit_simple]
private theorem Y_neg (i : Fin 4) (t : CoefficientField m) : Y i t = negativeUnit (s i) t := by
  simp only [Y, F4Chevalley.rootCurve, F4Chevalley.integralOperators,
    ← typeF4RootPairing_baseEquiv_val, rootCurveUnit_neg_simple]
private theorem node_ne : s 0 ≠ s 3 := by
  intro h
  have := typeF4RootPairing_baseEquiv.injective h
  contradiction
private theorem X_X (t u : CoefficientField m) : Commute (X 0 t) (X 3 u) := by
  rw [X_pos, X_pos]
  exact congrArg Subtype.val (commute_positive_positive_of_cartan_eq_zero (s 0) (s 3)
    node_ne (by rw [typeF4RootPairing_base_cartan_apply]; rfl) t u).eq
private theorem X_Y (t u : CoefficientField m) : Commute (X 0 t) (Y 3 u) := by
  rw [X_pos, Y_neg]
  exact congrArg Subtype.val (commute_positive_negative (s 0) (s 3) node_ne t u).eq
private theorem Y_X (t u : CoefficientField m) : Commute (Y 0 t) (X 3 u) := by
  rw [Y_neg, X_pos]
  exact (congrArg Subtype.val (commute_positive_negative (s 3) (s 0) node_ne.symm u t).eq).symm
private theorem L_true (t : CoefficientField m) : L true t = X 0 t * X 3 (theta m t) := rfl
private theorem L_false (t : CoefficientField m) : L false t = Y 0 t * Y 3 (theta m t) := rfl

private theorem W_one : W (1 : CoefficientField m) = titsUnit [s 0] * titsUnit [s 3] := by
  simp only [W, inv_one, L_true, L_false, map_one]
  rw [(Y_X 1 1).symm.mul_mul_mul_comm,
    ((X_X 1 1).symm.mul_left (X_Y 1 1).symm).mul_mul_mul_comm]
  simp only [titsUnit_cons, titsUnit_nil, mul_one, CharTwo.neg_eq,
    typeF4RootPairing_baseEquiv_val, X, Y, mul_assoc]

private theorem reflect_other (i j : Fin 4)
    (h : typeF4CartanMatrix j i = 0) :
    typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i)
      (typeF4SimpleRootIndex j) = typeF4SimpleRootIndex j := by
  apply typeF4RootPairing.reflectionPerm_eq_of_pairing_eq_zero
  rw [typeF4RootPairing_simpleIndex_pairing, h, map_zero]

private theorem simple_X_self (i : Fin 4) (t : CoefficientField m) :
    titsUnit [s i] * X i t * (titsUnit [s i])⁻¹ = Y i t :=
  simple_conj (s i) (typeF4SimpleRootIndex i) t

private theorem simple_X_other (i j : Fin 4) (h : typeF4CartanMatrix j i = 0)
    (t : CoefficientField m) :
    titsUnit [s i] * X j t * (titsUnit [s i])⁻¹ = X j t := by
  simpa only [X, typeF4RootPairing_baseEquiv_val, reflect_other i j h] using
    simple_conj (s i) (typeF4SimpleRootIndex j) t

private theorem simple_Y_other (i j : Fin 4) (h : typeF4CartanMatrix j i = 0)
    (t : CoefficientField m) :
    titsUnit [s i] * Y j t * (titsUnit [s i])⁻¹ = Y j t := by
  have hr : typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i)
      (-typeF4SimpleRootIndex j) = -typeF4SimpleRootIndex j := by
    apply typeF4RootPairing.reflectionPerm_eq_of_pairing_eq_zero
    simp only [RootPairing.indexNeg_neg, RootPairing.pairing_reflectionPerm_self_left,
      typeF4RootPairing_simpleIndex_pairing, h, map_zero, neg_zero]
  simpa only [Y, typeF4RootPairing_baseEquiv_val, hr] using
    simple_conj (s i) (-typeF4SimpleRootIndex j) t

private theorem W_one_conj (t : CoefficientField m) :
    W 1 * L true t * (W 1)⁻¹ = L false t := by
  rw [W_one, L_true, L_false]
  have he : ∀ n k x y : MatrixUnits m,
      (n * k) * (x * y) * (n * k)⁻¹ =
      (n * (k * x * k⁻¹) * n⁻¹) * (n * (k * y * k⁻¹) * n⁻¹) := by
    intros; group
  rw [he]
  rw [simple_X_other 3 0 rfl, simple_X_self, simple_X_self, simple_Y_other 0 3 rfl]

private theorem W_conj (b : (CoefficientField m)ˣ) (t : CoefficientField m) :
    W (b : CoefficientField m) * L true t * (W (b : CoefficientField m))⁻¹ =
      L false ((b : CoefficientField m)⁻¹ ^ 2 * t) := by
  let e := matrixTorusConj (blockTorus b 1)
  have he (p : Bool) (v : CoefficientField m) :
      e (L p v) = L p ((signedScale b p : CoefficientField m) * v) :=
    blockTorus_linearWord b 1 p v
  have hw : e (W 1) = W (b : CoefficientField m) := by
    simp only [W, map_mul, inv_one, he, signedScale, ↓reduceIte,
      Bool.false_eq_true, Units.val_inv_eq_inv_val, mul_one]
  have h := congrArg e (W_one_conj ((b : CoefficientField m)⁻¹ * t))
  simp only [map_mul, map_inv, hw, he, signedScale, ↓reduceIte,
    Bool.false_eq_true, Units.val_inv_eq_inv_val] at h
  simpa only [← mul_assoc, mul_inv_cancel₀ b.ne_zero, one_mul, pow_two] using h

def linearWeylWord (d : LocalBlockInput m) (t : CoefficientField m) : d.fixedGroup :=
  linearElement d true t * linearElement d false t⁻¹ * linearElement d true t

theorem linearWeylWord_conj (d : LocalBlockInput m) (t : CoefficientField m) (ht : t ≠ 0)
    (v : CoefficientField m) :
    linearWeylWord d t * linearElement d true v * (linearWeylWord d t)⁻¹ =
      linearElement d false (t⁻¹ ^ 2 * v) := by
  apply Subtype.ext
  apply Subtype.ext
  simpa only [linearWeylWord, Subgroup.coe_mul, Subgroup.coe_inv, linearElement_word,
    W, L, Units.val_mk0] using W_conj (Units.mk0 t ht) v

@[simp] theorem linearElement_zero (d : LocalBlockInput m) (p : Bool) :
    linearElement d p 0 = 1 :=
  congrArg Subtype.val ((linearEquiv d p).map_one)

@[simp] theorem linearElement_inv (d : LocalBlockInput m) (p : Bool) (t : CoefficientField m) :
    (linearElement d p t)⁻¹ = linearElement d p t := by
  apply inv_eq_of_mul_eq_one_left
  rw [← linearElement_add, CharTwo.add_self_eq_zero, linearElement_zero]

theorem linearElement_braid (d : LocalBlockInput m) (t : CoefficientField m) (ht : t ≠ 0) :
    linearElement d true t * linearElement d false t⁻¹ * linearElement d true t =
      linearElement d false t⁻¹ * linearElement d true t * linearElement d false t⁻¹ := by
  have h := linearWeylWord_conj d t ht t
  have hs : t⁻¹ ^ 2 * t = t⁻¹ := by field_simp
  rw [hs] at h
  have he := (mul_inv_eq_iff_eq_mul).mp h
  dsimp only [linearWeylWord] at he
  have he' := congrArg (· * linearElement d true t) he
  simpa only [mul_assoc, ← linearElement_add, CharTwo.add_self_eq_zero,
    linearElement_zero, mul_one] using he'

end ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery

end
