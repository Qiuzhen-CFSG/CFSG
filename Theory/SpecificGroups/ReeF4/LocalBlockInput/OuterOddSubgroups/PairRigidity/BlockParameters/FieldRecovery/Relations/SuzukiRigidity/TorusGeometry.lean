module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Relations.Actions
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.TorusCharacters

/-!
# The end-node torus as a word in the linear Ree blocks

A paired Weyl word is the product of the Weyl words on the two orthogonal
end nodes. Identifying each coroot word with its diagonal matrix shows that
a quotient of paired Weyl words is the end-node torus. Its characters on a
Suzuki block are the inverse torus parameter and its Suzuki norm.

The word uses only the two linear blocks, so its image under a signed linear
action is explicit. This is an arbitrary-automorphism calculation; no inner
realization of the recovered two-dimensional torus is assumed.

The private coroot calculation adapts the proof in
`ParabolicAmalgam/OuterLocal/SuzukiCommutators/TorusScaling.lean` without
changing that shared module. Sources: GLS3, Table 2.4, §§2.4–2.5, especially
2.4.5(d) and 2.5.1(b,c), in `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery.SuzukiRigidity
open RootPairing.IntegralGeckConstruction
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Parabolics
variable {m : ℕ}

private abbrev diag (m : ℕ) (i : Fin 4) (u : (CoefficientField m)ˣ) :=
  integralChevalleyTorusElement (P := typeF4RootPairing)
    (integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv i) u)

private theorem diag_tits (m : ℕ) (i : Fin 4) (u : (CoefficientField m)ˣ) :
    rootCurveTitsWord (S := CoefficientField m) [typeF4RootPairing_baseEquiv i] * diag m i u =
      (diag m i u)⁻¹ * rootCurveTitsWord (S := CoefficientField m)
        [typeF4RootPairing_baseEquiv i] := by
  apply Units.ext
  change specializeMatrix (titsWord [typeF4RootPairing_baseEquiv i]) * Matrix.diagonal _ =
    Matrix.diagonal _ * specializeMatrix (titsWord [typeF4RootPairing_baseEquiv i])
  simp only [titsWord, Matrix.mul_one]
  ext row col
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hz : titsLift (typeF4RootPairing_baseEquiv i) row col = 0
  · simp [specializeMatrix, hz]
  · have hw := titsLift_respectsChevalleyGrading (typeF4RootPairing_baseEquiv i)
      row col hz (typeF4SimpleRootIndex i)
    have hn : chevalleyBasisWeight (P := typeF4RootPairing) row (typeF4SimpleRootIndex i) =
        -chevalleyBasisWeight (P := typeF4RootPairing) col (typeF4SimpleRootIndex i) := by
      rw [hw]
      cases col with
      | inl j => simp [chevalleyBasisWeight]
      | inr j =>
        exact typeF4RootPairing.pairingIn_reflectionPerm_self_right ℤ j _
    have heval (a : F4Chevalley.BasisIndex) :
        chevalleyBasisTorusUnit (P := typeF4RootPairing)
          (integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv i) u) a =
        u ^ (-chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4SimpleRootIndex i)) := by
      unfold chevalleyBasisTorusUnit integralChevalleySimpleCorootParameter
      rw [Finset.prod_eq_single (typeF4RootPairing_baseEquiv i)]
      · simp only [if_true, typeF4RootPairing_baseEquiv_val]
      · intro j _ hj
        simp [hj]
      · simp
    have hu : chevalleyBasisTorusUnit (P := typeF4RootPairing)
        (integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv i) u) col =
        (chevalleyBasisTorusUnit (P := typeF4RootPairing)
        (integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv i) u) row)⁻¹ := by
      rw [heval, heval, hn]
      simp

    rw [hu]
    exact mul_comm _ _

noncomputable local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem diag_root (m : ℕ) (i : Fin 4) (u : (CoefficientField m)ˣ)
    (r : F4Chevalley.Root) (t : CoefficientField m) :
    (diag m i u)⁻¹ * F4Chevalley.rootCurve r t * diag m i u =
      F4Chevalley.rootCurve r
        (((u ^ typeF4RootPairing.pairingIn ℤ r (typeF4SimpleRootIndex i) :
          (CoefficientField m)ˣ) : CoefficientField m) * t) := by
  exact integralChevalleyRootCurve_simpleCoroot_conjugation
    (typeF4RootPairing_baseEquiv i) u r t

private theorem diag_mul (m : ℕ) (i : Fin 4) (u v : (CoefficientField m)ˣ) :
    diag m i (u * v) = diag m i u * diag m i v := by
  rw [diag, ← integralChevalleyTorusElement_mul]
  congr 1
  funext j
  simp only [integralChevalleySimpleCorootParameter, Pi.mul_apply]
  split_ifs <;> simp

private theorem weyl_one (m : ℕ) (i : Fin 4) :
    (weylWord m (typeF4SimpleRootIndex i) 1).val =
      rootCurveTitsWord (S := CoefficientField m) [typeF4RootPairing_baseEquiv i] := by
  rw [rootCurveTitsWord_cons, rootCurveTitsWord_nil, mul_one]
  change F4Chevalley.rootCurve _ 1 * F4Chevalley.rootCurve _ (-1⁻¹) *
    F4Chevalley.rootCurve _ 1 = _
  simp only [F4Chevalley.rootCurve, F4Chevalley.integralOperators,
    ← typeF4RootPairing_baseEquiv_val, rootCurveUnit_simple, rootCurveUnit_neg_simple,
    inv_one]

private theorem weyl_neg_one (m : ℕ) (i : Fin 4) :
    weylWord m (typeF4SimpleRootIndex i) (-1) =
      (weylWord m (typeF4SimpleRootIndex i) 1)⁻¹ := by
  apply Subtype.ext
  change F4Chevalley.rootCurve _ (-1) * F4Chevalley.rootCurve _ (-(-1)⁻¹) *
      F4Chevalley.rootCurve _ (-1) =
    (F4Chevalley.rootCurve _ 1 * F4Chevalley.rootCurve _ (-1⁻¹) *
      F4Chevalley.rootCurve _ 1)⁻¹
  simp [mul_inv_rev, F4Chevalley.rootCurve_inv, mul_assoc]

private theorem weyl_square (m : ℕ) (i : Fin 4) (u : (CoefficientField m)ˣ) :
    (weylWord m (typeF4SimpleRootIndex i) (u ^ 2)).val =
      (diag m i u)⁻¹ * (weylWord m (typeF4SimpleRootIndex i) 1).val * diag m i u := by
  change F4Chevalley.rootCurve _ _ * F4Chevalley.rootCurve _ _ *
    F4Chevalley.rootCurve _ _ =
    (diag m i u)⁻¹ * (F4Chevalley.rootCurve _ 1 * F4Chevalley.rootCurve _ (-1⁻¹) *
    F4Chevalley.rootCurve _ 1) * diag m i u
  symm
  calc
    _ = ((diag m i u)⁻¹ * F4Chevalley.rootCurve (typeF4SimpleRootIndex i) 1 * diag m i u) *
        ((diag m i u)⁻¹ * F4Chevalley.rootCurve (-typeF4SimpleRootIndex i) (-1⁻¹) * diag m i u) *
        ((diag m i u)⁻¹ * F4Chevalley.rootCurve (typeF4SimpleRootIndex i) 1 * diag m i u) := by group
    _ = _ := by simp [diag_root]

private theorem torus_square (m : ℕ) (i : Fin 4) (u : (CoefficientField m)ˣ) :
    (torusWord m (typeF4SimpleRootIndex i) (u ^ 2)).val = (diag m i (u ^ 2))⁻¹ := by
  change (weylWord m _ (u ^ 2)).val * (weylWord m _ (-1)).val = _
  rw [weyl_square, weyl_neg_one]
  change (diag m i u)⁻¹ * (weylWord m _ 1).val * diag m i u *
    ((weylWord m _ 1).val)⁻¹ = _
  rw [weyl_one, mul_assoc (diag m i u)⁻¹, diag_tits]
  rw [pow_two, diag_mul, mul_inv_rev]
  group



private theorem torus_matrix (i : Fin 4) (u : (CoefficientField m)ˣ) :
    (torusWord m (typeF4SimpleRootIndex i) u).val = (diag m i u)⁻¹ := by
  obtain ⟨v, hv⟩ := Finite.surjective_of_injective
    (show Function.Injective (fun x : (CoefficientField m)ˣ => x ^ 2) from by
      intro x y h
      apply Units.ext
      exact CharTwo.sq_injective (congrArg Units.val h)) u
  rw [← hv]
  exact torus_square m i v

private theorem weyl_matrix (i : Fin 4) (u : (CoefficientField m)ˣ) :
    (weylWord m (typeF4SimpleRootIndex i) u).val =
      (diag m i u)⁻¹ * (weylWord m (typeF4SimpleRootIndex i) 1).val := by
  have h := torus_matrix i u
  change (weylWord m _ u).val * (weylWord m _ (-1)).val = _ at h
  rw [weyl_neg_one] at h
  exact (mul_inv_eq_iff_eq_mul).mp h

private theorem end_commute (p q : Bool) (t u : CoefficientField m) :
    Commute (rootGeneratorInGroup m (signedRoot p (typeF4SimpleRootIndex 0)) t)
      (rootGeneratorInGroup m (signedRoot q (typeF4SimpleRootIndex 3)) u) := by
  have hne : typeF4RootPairing_baseEquiv 0 ≠ typeF4RootPairing_baseEquiv 3 := by
    intro h
    have := typeF4RootPairing_baseEquiv.injective h
    contradiction
  have hc : typeF4RootPairing_base.cartanMatrix
      (typeF4RootPairing_baseEquiv 3) (typeF4RootPairing_baseEquiv 0) = 0 := by
    rw [typeF4RootPairing_base_cartan_apply]
    norm_num [typeF4CartanMatrix, Fin.ext_iff]
  apply Subtype.ext
  cases p <;> cases q
  all_goals
    simp only [signedRoot, Bool.false_eq_true, ↓reduceIte]
    change F4Chevalley.rootCurve _ t * F4Chevalley.rootCurve _ u =
      F4Chevalley.rootCurve _ u * F4Chevalley.rootCurve _ t
    simp only [F4Chevalley.rootCurve, F4Chevalley.integralOperators,
      ← typeF4RootPairing_baseEquiv_val, rootCurveUnit_simple, rootCurveUnit_neg_simple]
  · exact congrArg Subtype.val
      (RootPairing.SimpleGeckGroup.commute_negative_negative_of_cartan_eq_zero _ _ hne hc t u).eq
  · exact congrArg Subtype.val
      (RootPairing.SimpleGeckGroup.commute_positive_negative _ _ hne.symm u t).eq.symm
  · exact congrArg Subtype.val
      (RootPairing.SimpleGeckGroup.commute_positive_negative _ _ hne t u).eq
  · exact congrArg Subtype.val
      (RootPairing.SimpleGeckGroup.commute_positive_positive_of_cartan_eq_zero _ _ hne hc t u).eq

/-- The paired Weyl word, expressed entirely in the signed linear blocks. -/
def linearWeyl (d : LocalBlockInput m) (u : (CoefficientField m)ˣ) : d.fixedGroup :=
  linearElement d true u * linearElement d false (u⁻¹ : (CoefficientField m)ˣ) *
    linearElement d true u

private theorem linearWeyl_split (d : LocalBlockInput m) (u : (CoefficientField m)ˣ) :
    (linearWeyl d u).val = weylWord m (typeF4SimpleRootIndex 0) u *
      weylWord m (typeF4SimpleRootIndex 3) (theta m u) := by
  simp only [linearWeyl, Subgroup.coe_mul, linearElement_word]
  simp only [linearWord, linearRoots, signedRoot, Bool.false_eq_true, ↓reduceIte,
    Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_inv_eq_inv_val, map_inv₀,
    weylWord, CharTwo.neg_eq]
  have h1 := (end_commute false true ((u : CoefficientField m)⁻¹) (theta m u)).symm
  have h2 := (end_commute true false (u : CoefficientField m) ((theta m u)⁻¹)).symm
  have h3 := (end_commute true true (u : CoefficientField m) (theta m u)).symm
  simp only [signedRoot, Bool.false_eq_true, ↓reduceIte] at h1 h2 h3
  calc
    _ = (rootGeneratorInGroup m (typeF4SimpleRootIndex 0) u *
          rootGeneratorInGroup m (-typeF4SimpleRootIndex 0) (u : CoefficientField m)⁻¹) *
        ((rootGeneratorInGroup m (typeF4SimpleRootIndex 3) (theta m u) *
          rootGeneratorInGroup m (-typeF4SimpleRootIndex 3) (theta m u)⁻¹) *
        (rootGeneratorInGroup m (typeF4SimpleRootIndex 0) u *
          rootGeneratorInGroup m (typeF4SimpleRootIndex 3) (theta m u))) := by
      simp only [mul_assoc]
      rw [h1.left_comm]
    _ = _ := by
      rw [(h3.mul_left h2).left_comm]
      simp only [mul_assoc]
private theorem diag_weyl_end (u : (CoefficientField m)ˣ) :
    Commute (diag m 3 u) (weylWord m (typeF4SimpleRootIndex 0) 1).val := by
  have hroot (p : Bool) (t : CoefficientField m) :
      Commute (diag m 3 u) (F4Chevalley.rootCurve (signedRoot p (typeF4SimpleRootIndex 0)) t) := by
    have h := diag_root m 3 u (signedRoot p (typeF4SimpleRootIndex 0)) t
    have hz : typeF4RootPairing.pairingIn ℤ
        (signedRoot p (typeF4SimpleRootIndex 0)) (typeF4SimpleRootIndex 3) = 0 := by
      cases p <;> simp only [signedRoot, Bool.false_eq_true, ↓reduceIte]
      · rw [RootPairing.indexNeg_neg, RootPairing.pairingIn_reflectionPerm_self_left]
        rw [show typeF4RootPairing.pairingIn ℤ (typeF4SimpleRootIndex 0)
          (typeF4SimpleRootIndex 3) = typeF4CartanMatrix 0 3 from
          typeF4RootPairing_base_cartan_apply 0 3]
        norm_num [typeF4CartanMatrix, Fin.ext_iff]
      · rw [show typeF4RootPairing.pairingIn ℤ (typeF4SimpleRootIndex 0)
          (typeF4SimpleRootIndex 3) = typeF4CartanMatrix 0 3 from
          typeF4RootPairing_base_cartan_apply 0 3]
        norm_num [typeF4CartanMatrix, Fin.ext_iff]
    simp only [hz, zpow_zero, Units.val_one, one_mul] at h
    change _ * _ = _ * _
    calc
      _ = diag m 3 u * ((diag m 3 u)⁻¹ *
          F4Chevalley.rootCurve (signedRoot p (typeF4SimpleRootIndex 0)) t * diag m 3 u) := by rw [h]
      _ = _ := by group
  exact ((hroot true 1).mul_right (hroot false (-1⁻¹))).mul_right (hroot true 1)

private def endParameters (u : (CoefficientField m)ˣ) : TorusParameters m :=
  integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv 0) u *
    integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv 3)
      (Units.map (theta m : CoefficientField m →* CoefficientField m) u)

private theorem endParameters_block (u : (CoefficientField m)ˣ) :
    endParameters u = blockTorus (u ^ 2) u⁻¹ := by
  funext q
  obtain ⟨i, rfl⟩ := typeF4RootPairing_baseEquiv.surjective q
  fin_cases i
  all_goals
    simp [endParameters, integralChevalleySimpleCorootParameter, blockTorus,
      torusParametersOfSimpleScales, Fin.ext_iff, map_pow]
    group

private theorem linearWeyl_matrix (d : LocalBlockInput m) (u : (CoefficientField m)ˣ) :
    (linearWeyl d u).val.val =
      (torusMatrix (endParameters u))⁻¹ * (linearWeyl d 1).val.val := by
  rw [linearWeyl_split, linearWeyl_split]
  change (weylWord m _ u).val * (weylWord m _ (theta m u)).val =
    _ * ((weylWord m _ 1).val * (weylWord m _ (theta m 1)).val)
  rw [map_one]
  rw [weyl_matrix 0 u, show theta m (u : CoefficientField m) =
    (Units.map (theta m : CoefficientField m →* CoefficientField m) u : CoefficientField m) from rfl,
    weyl_matrix 3]
  change _ = (integralChevalleyTorusElement (endParameters u))⁻¹ * _
  rw [endParameters, integralChevalleyTorusElement_mul, mul_inv_rev]
  change _ = ((diag m 3 _)⁻¹ * (diag m 0 u)⁻¹) * _
  have hd : Commute (diag m 0 u) (diag m 3
      (Units.map (theta m : CoefficientField m →* CoefficientField m) u)) := by
    change _ * _ = _ * _
    simp only [diag, ← integralChevalleyTorusElement_mul, mul_comm]
  rw [← hd.inv_inv.eq]
  simp only [mul_assoc]
  rw [(diag_weyl_end _).inv_left.symm.left_comm]

private theorem endParameters_mul (s t : (CoefficientField m)ˣ) :
    endParameters (s * t) = endParameters s * endParameters t := by
  funext q
  simp only [endParameters, Pi.mul_apply, integralChevalleySimpleCorootParameter,
    map_mul]
  split_ifs <;> simp [mul_mul_mul_comm]

private theorem endParameters_inv (s : (CoefficientField m)ˣ) :
    endParameters s⁻¹ = (endParameters s)⁻¹ := by
  funext q
  simp only [endParameters, Pi.mul_apply, Pi.inv_apply, integralChevalleySimpleCorootParameter,
    map_inv]
  split_ifs <;> simp [mul_comm]

private theorem linearWeyl_ratio_matrix (d : LocalBlockInput m)
    (s t : (CoefficientField m)ˣ) :
    ((linearWeyl d s * (linearWeyl d t)⁻¹).val.val) =
      (torusMatrix (endParameters (s * t⁻¹)))⁻¹ := by
  change (linearWeyl d s).val.val * ((linearWeyl d t).val.val)⁻¹ = _
  rw [linearWeyl_matrix d s, linearWeyl_matrix d t, endParameters_mul, endParameters_inv]
  change _ = (integralChevalleyTorusElement (endParameters s * (endParameters t)⁻¹))⁻¹
  rw [integralChevalleyTorusElement_mul, integralChevalleyTorusElement_inv]
  have hc : Commute (torusMatrix (endParameters s)) (torusMatrix (endParameters t)) := by
    change integralChevalleyTorusElement (endParameters s) * integralChevalleyTorusElement (endParameters t) =
      integralChevalleyTorusElement (endParameters t) * integralChevalleyTorusElement (endParameters s)
    rw [← integralChevalleyTorusElement_mul, ← integralChevalleyTorusElement_mul, mul_comm (endParameters s) (endParameters t)]
  calc
    _ = (torusMatrix (endParameters s))⁻¹ * torusMatrix (endParameters t) := by group
    _ = _ := by rw [hc.inv_left.eq]; rfl
/-- The word in the two linear blocks used for a rank-one Weyl element
has its parameter transformed by the prescribed signed linear action. -/
theorem linearWeyl_action (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (b : (CoefficientField m)ˣ) (σ : CoefficientField m ≃+* CoefficientField m)
    (hlin : SignedLinearAction d a b σ) (s : (CoefficientField m)ˣ) :
    a (linearWeyl d s) = linearWeyl d (b * Units.map σ.toMonoidHom s) := by
  have hp : (signedScale b true : CoefficientField m) * σ (s : CoefficientField m) =
      ((b * Units.map σ.toMonoidHom s : (CoefficientField m)ˣ) : CoefficientField m) := rfl
  have hn : (signedScale b false : CoefficientField m) * σ (s⁻¹ : (CoefficientField m)ˣ) =
      (((b * Units.map σ.toMonoidHom s)⁻¹ : (CoefficientField m)ˣ) : CoefficientField m) := by
    simp only [signedScale, Bool.false_eq_true, ↓reduceIte, Units.val_inv_eq_inv_val,
      Units.val_mul, Units.coe_map, map_inv₀, mul_inv_rev]
    exact mul_comm _ _
  unfold linearWeyl
  rw [map_mul, map_mul, hlin, hlin, hp, hn]


/-- A quotient of paired Weyl words has the first and central Suzuki characters
of the end-node coroot torus. -/
theorem linearWeyl_ratio_suzuki (d : LocalBlockInput m) (C : SuzukiCoordinates d)
    (s t : (CoefficientField m)ˣ) (positive : Bool) (v w : CoefficientField m) :
    (linearWeyl d s * (linearWeyl d t)⁻¹) * C.element positive v w *
        (linearWeyl d s * (linearWeyl d t)⁻¹)⁻¹ =
      C.element positive
        ((signedScale (s * t⁻¹)⁻¹ positive : CoefficientField m) * v)
        ((signedScale (centralScale (s * t⁻¹)⁻¹) positive : CoefficientField m) * w) := by
  apply Subtype.ext
  apply Subtype.ext
  change ((linearWeyl d s * (linearWeyl d t)⁻¹).val.val) *
      (suzukiWord m positive v w).val *
      ((linearWeyl d s * (linearWeyl d t)⁻¹).val.val)⁻¹ = _
  rw [linearWeyl_ratio_matrix, endParameters_block, inv_inv]
  exact blockTorus_suzukiWord ((s * t⁻¹) ^ 2) (s * t⁻¹)⁻¹ positive v w

end ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery.SuzukiRigidity
end
