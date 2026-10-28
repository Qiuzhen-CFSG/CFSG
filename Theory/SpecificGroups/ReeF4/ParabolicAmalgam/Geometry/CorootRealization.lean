module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.DiagonalTorus
public import Theory.AlgebraicGroup.RootSystems.IntegralRootCurveSimpleGeneration

/-!
# Coroot words realize the diagonal F₄ torus

The unchanged rank-one word `torusWord` equals the diagonal simple-coroot
matrix with inverse parameter. To calculate it, first conjugate the unit
Weyl word by a diagonal element, then use the Tits lift's action on basis
weights. Squaring is surjective in the finite characteristic-two coefficient
field, so this proves the formula for every nonzero parameter, including
at `m = 0`.

The chosen integral Tits routes transport positive and negative root words
to simple-root words. An entrywise weight calculation shows that each Tits
lift normalizes the diagonal image. Thus every coroot word lies in that
image. Conversely, decomposing a torus parameter into its four simple-coroot
coordinates expresses every diagonal matrix as a product of coroot words
in the actual split carrier.

The simple-coroot calculation adapts the existing proof in
`ParabolicAmalgam/OuterLocal/SuzukiCommutators/TorusScaling.lean`.
This is the coroot realization used in the Ree parabolic construction for
Aschbacher–Smith F.1.4–5 and F.1.12(I)(5), printed pp.260,263–264 of
`refs/quasithin.pdf`; the integral root construction follows Steinberg,
*Lectures on Chevalley Groups*, Theorem 1 and Lemmas 5–6.
-/

public section

open RootPairing.IntegralGeckConstruction
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped BigOperators
noncomputable section
namespace ReeF4.Parabolics

private abbrev diag (m : ℕ) (i : typeF4RootPairing_base.support) (u : (CoefficientField m)ˣ) :=
  integralChevalleyTorusElement (P := typeF4RootPairing)
    (integralChevalleySimpleCorootParameter i u)

private theorem diag_tits (m : ℕ) (i : typeF4RootPairing_base.support) (u : (CoefficientField m)ˣ) :
    rootCurveTitsWord (S := CoefficientField m) [i] * diag m i u =
      (diag m i u)⁻¹ * rootCurveTitsWord (S := CoefficientField m)
        [i] := by
  apply Units.ext
  change specializeMatrix (titsWord [i]) * Matrix.diagonal _ =
    Matrix.diagonal _ * specializeMatrix (titsWord [i])
  simp only [titsWord, Matrix.mul_one]
  ext row col
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hz : titsLift i row col = 0
  · simp [specializeMatrix, hz]
  · have hw := titsLift_respectsChevalleyGrading i
      row col hz (i : F4Chevalley.Root)
    have hn : chevalleyBasisWeight (P := typeF4RootPairing) row (i : F4Chevalley.Root) =
        -chevalleyBasisWeight (P := typeF4RootPairing) col (i : F4Chevalley.Root) := by
      rw [hw]
      cases col with
      | inl j => simp [chevalleyBasisWeight]
      | inr j =>
        exact typeF4RootPairing.pairingIn_reflectionPerm_self_right ℤ j _
    have heval (a : F4Chevalley.BasisIndex) :
        chevalleyBasisTorusUnit (P := typeF4RootPairing)
          (integralChevalleySimpleCorootParameter i u) a =
        u ^ (-chevalleyBasisWeight (P := typeF4RootPairing) a (i : F4Chevalley.Root)) := by
      unfold chevalleyBasisTorusUnit integralChevalleySimpleCorootParameter
      rw [Finset.prod_eq_single i]
      · simp only [if_true]
      · intro j _ hj
        simp [hj]
      · simp
    have hu : chevalleyBasisTorusUnit (P := typeF4RootPairing)
        (integralChevalleySimpleCorootParameter i u) col =
        (chevalleyBasisTorusUnit (P := typeF4RootPairing)
        (integralChevalleySimpleCorootParameter i u) row)⁻¹ := by
      rw [heval, heval, hn]
      simp

    rw [hu]
    exact mul_comm _ _

noncomputable local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem diag_root (m : ℕ) (i : typeF4RootPairing_base.support) (u : (CoefficientField m)ˣ)
    (r : F4Chevalley.Root) (t : CoefficientField m) :
    (diag m i u)⁻¹ * F4Chevalley.rootCurve r t * diag m i u =
      F4Chevalley.rootCurve r
        (((u ^ typeF4RootPairing.pairingIn ℤ r (i : F4Chevalley.Root) :
          (CoefficientField m)ˣ) : CoefficientField m) * t) := by
  exact integralChevalleyRootCurve_simpleCoroot_conjugation
    i u r t

private theorem diag_mul (m : ℕ) (i : typeF4RootPairing_base.support) (u v : (CoefficientField m)ˣ) :
    diag m i (u * v) = diag m i u * diag m i v := by
  rw [diag, ← integralChevalleyTorusElement_mul]
  congr 1
  funext j
  simp only [integralChevalleySimpleCorootParameter, Pi.mul_apply]
  split_ifs <;> simp

private theorem weyl_one (m : ℕ) (i : typeF4RootPairing_base.support) :
    (weylWord m (i : F4Chevalley.Root) 1).val =
      rootCurveTitsWord (S := CoefficientField m) [i] := by
  rw [rootCurveTitsWord_cons, rootCurveTitsWord_nil, mul_one]
  change F4Chevalley.rootCurve _ 1 * F4Chevalley.rootCurve _ (-1⁻¹) *
    F4Chevalley.rootCurve _ 1 = _
  simp only [F4Chevalley.rootCurve, F4Chevalley.integralOperators,
    rootCurveUnit_simple, rootCurveUnit_neg_simple,
    inv_one]

private theorem weyl_neg_one (m : ℕ) (i : typeF4RootPairing_base.support) :
    weylWord m (i : F4Chevalley.Root) (-1) =
      (weylWord m (i : F4Chevalley.Root) 1)⁻¹ := by
  apply Subtype.ext
  change F4Chevalley.rootCurve _ (-1) * F4Chevalley.rootCurve _ (-(-1)⁻¹) *
      F4Chevalley.rootCurve _ (-1) =
    (F4Chevalley.rootCurve _ 1 * F4Chevalley.rootCurve _ (-1⁻¹) *
      F4Chevalley.rootCurve _ 1)⁻¹
  simp [mul_inv_rev, F4Chevalley.rootCurve_inv, mul_assoc]

private theorem weyl_square (m : ℕ) (i : typeF4RootPairing_base.support) (u : (CoefficientField m)ˣ) :
    (weylWord m (i : F4Chevalley.Root) (u ^ 2)).val =
      (diag m i u)⁻¹ * (weylWord m (i : F4Chevalley.Root) 1).val * diag m i u := by
  change F4Chevalley.rootCurve _ _ * F4Chevalley.rootCurve _ _ *
    F4Chevalley.rootCurve _ _ =
    (diag m i u)⁻¹ * (F4Chevalley.rootCurve _ 1 * F4Chevalley.rootCurve _ (-1⁻¹) *
    F4Chevalley.rootCurve _ 1) * diag m i u
  symm
  calc
    _ = ((diag m i u)⁻¹ * F4Chevalley.rootCurve (i : F4Chevalley.Root) 1 * diag m i u) *
        ((diag m i u)⁻¹ * F4Chevalley.rootCurve (-(i : F4Chevalley.Root)) (-1⁻¹) * diag m i u) *
        ((diag m i u)⁻¹ * F4Chevalley.rootCurve (i : F4Chevalley.Root) 1 * diag m i u) := by group
    _ = _ := by simp [diag_root]

private theorem torus_square (m : ℕ) (i : typeF4RootPairing_base.support) (u : (CoefficientField m)ˣ) :
    (torusWord m (i : F4Chevalley.Root) (u ^ 2)).val = (diag m i (u ^ 2))⁻¹ := by
  change (weylWord m _ (u ^ 2)).val * (weylWord m _ (-1)).val = _
  rw [weyl_square, weyl_neg_one]
  change (diag m i u)⁻¹ * (weylWord m _ 1).val * diag m i u *
    ((weylWord m _ 1).val)⁻¹ = _
  rw [weyl_one, mul_assoc (diag m i u)⁻¹, diag_tits]
  rw [pow_two, diag_mul, mul_inv_rev]
  group

private theorem unit_square_surjective (m : ℕ) (t : (CoefficientField m)ˣ) :
    ∃ u : (CoefficientField m)ˣ, u ^ 2 = t := by
  apply Finite.surjective_of_injective (f := fun u : (CoefficientField m)ˣ => u ^ 2) _ t
  intro u v huv
  apply Units.ext
  have h := congrArg Units.val huv
  exact (frobenius_inj (CoefficientField m) 2) h

/-- The coroot word uses the inverse of the diagonal parameter convention. -/
theorem torusWord_simple_coe (m : ℕ) (i : typeF4RootPairing_base.support)
    (t : (CoefficientField m)ˣ) :
    (torusWord m i t).val = diagonalTorusHom m
      (integralChevalleySimpleCorootParameter i t⁻¹) := by
  obtain ⟨u, rfl⟩ := unit_square_surjective m t
  rw [torus_square]
  change (diag m i (u ^ 2))⁻¹ = diag m i ((u ^ 2)⁻¹)
  rw [diag, ← integralChevalleyTorusElement_inv]
  congr 1
  funext j
  simp only [integralChevalleySimpleCorootParameter, Pi.inv_apply]
  split_ifs <;> simp

private theorem basisUnit_simple (m : ℕ) (q : typeF4RootPairing_base.support)
    (u : (CoefficientField m)ˣ) (a : F4Chevalley.BasisIndex) :
    chevalleyBasisTorusUnit (P := typeF4RootPairing)
      (integralChevalleySimpleCorootParameter q u) a =
      u ^ (-chevalleyBasisWeight (P := typeF4RootPairing) a q) := by
  unfold chevalleyBasisTorusUnit integralChevalleySimpleCorootParameter
  rw [Finset.prod_eq_single q]
  · simp
  · intro j _ hj; simp [hj]
  · simp

private theorem weight_reflection (a : F4Chevalley.BasisIndex)
    (i q : F4Chevalley.Root) :
    chevalleyBasisWeight (P := typeF4RootPairing) a (typeF4RootPairing.reflectionPerm i q) =
      chevalleyBasisWeight (P := typeF4RootPairing) a q -
        typeF4RootPairing.pairingIn ℤ i q * chevalleyBasisWeight (P := typeF4RootPairing) a i := by
  cases a with
  | inl j => simp [chevalleyBasisWeight]
  | inr r =>
    simp only [chevalleyBasisWeight, typeF4RootPairing.pairingIn_reflectionPerm]
    have hr : typeF4RootPairing.root (typeF4RootPairing.reflectionPerm i r) =
        (1 : ℤ) • typeF4RootPairing.root r +
          (-typeF4RootPairing.pairingIn ℤ r i) • typeF4RootPairing.root i := by
      rw [typeF4RootPairing.root_reflectionPerm, typeF4RootPairing.reflection_apply_root]
      simp [sub_eq_add_neg, ← typeF4RootPairing.algebraMap_pairingIn ℤ,
        Int.cast_smul_eq_zsmul]
    simpa [smul_eq_mul, sub_eq_add_neg, mul_comm] using
      (typeF4RootPairing.pairingIn_eq_add_of_root_eq_smul_add_smul (S := ℤ) (j := q) hr)

private theorem tits_simple_diag (m : ℕ) (i q : typeF4RootPairing_base.support)
    (u : (CoefficientField m)ˣ) :
    rootCurveTitsWord [i] * diag m q u =
      (diag m q u * diag m i (u ^ (-typeF4RootPairing.pairingIn ℤ i q))) *
        rootCurveTitsWord [i] := by
  apply Units.ext
  change specializeMatrix (titsWord [i]) * Matrix.diagonal _ =
    (Matrix.diagonal _ * Matrix.diagonal _) * specializeMatrix (titsWord [i])
  simp only [titsWord, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
  ext row col
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hz : titsLift i row col = 0
  · simp [specializeMatrix, hz]
  · have hw := titsLift_respectsChevalleyGrading i row col hz
      (typeF4RootPairing.reflectionPerm i q)
    rw [typeF4RootPairing.reflectionPerm_self, weight_reflection] at hw
    have hu : chevalleyBasisTorusUnit (P := typeF4RootPairing)
        (integralChevalleySimpleCorootParameter q u) col =
        chevalleyBasisTorusUnit (P := typeF4RootPairing)
          (integralChevalleySimpleCorootParameter q u) row *
        chevalleyBasisTorusUnit (P := typeF4RootPairing)
          (integralChevalleySimpleCorootParameter i
            (u ^ (-typeF4RootPairing.pairingIn ℤ i q))) row := by
      rw [basisUnit_simple, basisUnit_simple, basisUnit_simple, ← zpow_mul, ← zpow_add]
      congr 1
      rw [← hw]
      ring
    rw [hu, Units.val_mul]
    exact mul_comm _ _

private theorem parameter_prod_simple (m : ℕ) (u : TorusParameter m) :
    (∏ q, integralChevalleySimpleCorootParameter q (u q)) = u := by
  funext j
  simp only [Finset.prod_apply, integralChevalleySimpleCorootParameter]
  rw [Finset.prod_eq_single j]
  · simp
  · intro q _ hq; simp [Ne.symm hq]
  · simp

private theorem tits_conj_diagonal_mem (m : ℕ)
    (word : List typeF4RootPairing_base.support) (u : TorusParameter m) :
    rootCurveTitsWord word * diagonalTorusHom m u * (rootCurveTitsWord word)⁻¹ ∈
      (diagonalTorusHom m).range := by
  have hsimple (i : typeF4RootPairing_base.support) (v : TorusParameter m) :
      rootCurveTitsWord [i] * diagonalTorusHom m v * (rootCurveTitsWord [i])⁻¹ ∈
        (diagonalTorusHom m).range := by
    have hp (s : Finset typeF4RootPairing_base.support) :
        rootCurveTitsWord [i] * diagonalTorusHom m
          (∏ q ∈ s, integralChevalleySimpleCorootParameter q (v q)) *
          (rootCurveTitsWord [i])⁻¹ ∈ (diagonalTorusHom m).range := by
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.prod_empty, map_one, mul_one, mul_inv_cancel]
        exact Subgroup.one_mem _
      | @insert q s hq ih =>
        rw [Finset.prod_insert hq, map_mul]
        have he : rootCurveTitsWord (S := CoefficientField m) [i] *
            (diagonalTorusHom m (integralChevalleySimpleCorootParameter q (v q)) *
              diagonalTorusHom m (∏ j ∈ s, integralChevalleySimpleCorootParameter j (v j))) *
            (rootCurveTitsWord [i])⁻¹ =
            (rootCurveTitsWord [i] * diag m q (v q) * (rootCurveTitsWord [i])⁻¹) *
              (rootCurveTitsWord [i] *
                diagonalTorusHom m (∏ j ∈ s, integralChevalleySimpleCorootParameter j (v j)) *
                (rootCurveTitsWord [i])⁻¹) := by
          change _ = (rootCurveTitsWord [i] *
            diagonalTorusHom m (integralChevalleySimpleCorootParameter q (v q)) *
            (rootCurveTitsWord [i])⁻¹) * _
          group
        rw [he]
        apply Subgroup.mul_mem _ _ ih
        rw [tits_simple_diag, mul_assoc, mul_inv_cancel, mul_one]
        exact Subgroup.mul_mem _ ⟨_, rfl⟩ ⟨_, rfl⟩
    simpa only [parameter_prod_simple] using hp Finset.univ
  induction word generalizing u with
  | nil => simp
  | cons i word ih =>
    obtain ⟨v, hv⟩ := ih u
    have he : rootCurveTitsWord (S := CoefficientField m) (i :: word) =
        rootCurveTitsWord [i] * rootCurveTitsWord word := by
      simp only [rootCurveTitsWord_cons, rootCurveTitsWord_nil, mul_one]
    rw [he]
    have hreassoc : (rootCurveTitsWord [i] * rootCurveTitsWord word) * diagonalTorusHom m u *
        (rootCurveTitsWord [i] * rootCurveTitsWord word)⁻¹ =
        rootCurveTitsWord [i] *
          (rootCurveTitsWord word * diagonalTorusHom m u * (rootCurveTitsWord word)⁻¹) *
          (rootCurveTitsWord [i])⁻¹ := by group
    rw [hreassoc, ← hv]
    exact hsimple i v

private theorem specialize_e (m : ℕ) (i : typeF4RootPairing_base.support) (t : ℤ) :
    specializeMatrix (S := CoefficientField m) (eUnipotent i t) =
      RootPairing.SimpleGeckGroup.positiveMatrix i (t : CoefficientField m) := by
  ext j k
  simp only [specializeMatrix, eUnipotent, RootPairing.SimpleGeckGroup.positiveMatrix_formula,
    Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Int.coe_castRingHom, Int.cast_add, Int.cast_mul, Int.cast_pow]
  simp [Matrix.one_apply]

private theorem specialize_f (m : ℕ) (i : typeF4RootPairing_base.support) (t : ℤ) :
    specializeMatrix (S := CoefficientField m) (fUnipotent i t) =
      RootPairing.SimpleGeckGroup.negativeMatrix i (t : CoefficientField m) := by
  ext j k
  simp only [specializeMatrix, fUnipotent, RootPairing.SimpleGeckGroup.negativeMatrix_formula,
    Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Int.coe_castRingHom, Int.cast_add, Int.cast_mul, Int.cast_pow]
  simp [Matrix.one_apply]

private theorem weyl_negative_simple_one (m : ℕ) (i : typeF4RootPairing_base.support) :
    (weylWord m (-i : F4Chevalley.Root) 1).val = rootCurveTitsWord [i] := by
  have he : eUnipotent i 1 * eUnipotent i (-1) = 1 := by
    rw [eUnipotent_add]; simp
  have h := congrArg (fun A => A * eUnipotent i (-1)) (titsLift_mul_eUnipotent i 1)
  have ht : titsLift i = fUnipotent i (-1) * eUnipotent i 1 * fUnipotent i (-1) := by
    calc
      titsLift i = titsLift i * (eUnipotent i 1 * eUnipotent i (-1)) := by rw [he, Matrix.mul_one]
      _ = fUnipotent i (-1) * titsLift i * eUnipotent i (-1) := by
        rw [← Matrix.mul_assoc, h]
      _ = _ := by simp only [titsLift, Matrix.mul_assoc, he, Matrix.mul_one]
  apply Units.ext
  change (F4Chevalley.rootCurve (S := CoefficientField m) (-i : F4Chevalley.Root) 1 *
    F4Chevalley.rootCurve (-(-i) : F4Chevalley.Root) (-1⁻¹) *
    F4Chevalley.rootCurve (-i : F4Chevalley.Root) 1).val = specializeMatrix (S := CoefficientField m) (titsWord [i])
  simp only [neg_neg, F4Chevalley.rootCurve, F4Chevalley.integralOperators,
    rootCurveUnit_neg_simple, rootCurveUnit_simple, inv_one, CharTwo.neg_eq,
    Units.val_mul, RootPairing.SimpleGeckGroup.negativeUnit_val, RootPairing.SimpleGeckGroup.positiveUnit_val,
    titsWord, Matrix.mul_one, ht, specializeMatrix_mul, specialize_e, specialize_f,
    Int.cast_neg, Int.cast_one]

private theorem weyl_negative_square (m : ℕ) (i : typeF4RootPairing_base.support)
    (u : (CoefficientField m)ˣ) :
    (weylWord m (-i : F4Chevalley.Root) (u ^ 2)).val =
      (diag m i u⁻¹)⁻¹ * (weylWord m (-i : F4Chevalley.Root) 1).val * diag m i u⁻¹ := by
  change F4Chevalley.rootCurve _ _ * F4Chevalley.rootCurve _ _ * F4Chevalley.rootCurve _ _ =
    (diag m i u⁻¹)⁻¹ * (F4Chevalley.rootCurve _ 1 * F4Chevalley.rootCurve _ (-1⁻¹) *
      F4Chevalley.rootCurve _ 1) * diag m i u⁻¹
  symm
  calc
    _ = ((diag m i u⁻¹)⁻¹ * F4Chevalley.rootCurve (-i : F4Chevalley.Root) 1 * diag m i u⁻¹) *
        ((diag m i u⁻¹)⁻¹ * F4Chevalley.rootCurve (-(-i) : F4Chevalley.Root) (-1⁻¹) * diag m i u⁻¹) *
        ((diag m i u⁻¹)⁻¹ * F4Chevalley.rootCurve (-i : F4Chevalley.Root) 1 * diag m i u⁻¹) := by group
    _ = _ := by simp [diag_root]

/-- The negative simple root reverses the coroot parameter. -/
theorem torusWord_neg_simple_coe (m : ℕ) (i : typeF4RootPairing_base.support)
    (t : (CoefficientField m)ˣ) :
    (torusWord m (-i : F4Chevalley.Root) t).val =
      diagonalTorusHom m (integralChevalleySimpleCorootParameter i t) := by
  obtain ⟨u, rfl⟩ := unit_square_surjective m t
  have hw : weylWord m (-i : F4Chevalley.Root) (-1) =
      (weylWord m (-i : F4Chevalley.Root) 1)⁻¹ := by
    apply Subtype.ext
    change F4Chevalley.rootCurve _ (-1) * F4Chevalley.rootCurve _ (-(-1)⁻¹) *
        F4Chevalley.rootCurve _ (-1) =
      (F4Chevalley.rootCurve _ 1 * F4Chevalley.rootCurve _ (-1⁻¹) *
        F4Chevalley.rootCurve _ 1)⁻¹
    simp [mul_inv_rev, F4Chevalley.rootCurve_inv, mul_assoc]
  change (weylWord m _ (u ^ 2)).val * (weylWord m _ (-1)).val = diag m i (u ^ 2)
  rw [weyl_negative_square, hw]
  change (diag m i u⁻¹)⁻¹ * (weylWord m _ 1).val * diag m i u⁻¹ *
    ((weylWord m _ 1).val)⁻¹ = _
  rw [weyl_negative_simple_one, mul_assoc (diag m i u⁻¹)⁻¹, diag_tits]
  have hd : diag m i u⁻¹ = (diag m i u)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← diag_mul, inv_mul_cancel]
    have hp : integralChevalleySimpleCorootParameter i (1 : (CoefficientField m)ˣ) = 1 := by
      funext j
      simp [integralChevalleySimpleCorootParameter]
    change integralChevalleyTorusElement (integralChevalleySimpleCorootParameter i 1) = 1
    rw [hp, integralChevalleyTorusElement_one]
  rw [hd, inv_inv, pow_two, diag_mul]
  group

private theorem weylWord_pos_route (m : ℕ) (r : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (t : CoefficientField m) :
    (weylWord m r t).val =
      rootCurveTitsWord (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).word *
        (weylWord m (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).simple t).val *
        (rootCurveTitsWord (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).word)⁻¹ := by
  have hn : ¬ typeF4RootPairing_base.IsPos (-r) := by
    simpa only [RootPairing.Base.IsPos.neg_iff_not, not_not] using hr
  change F4Chevalley.rootCurve r t * F4Chevalley.rootCurve (-r) (-t⁻¹) *
    F4Chevalley.rootCurve r t = _ *
      (F4Chevalley.rootCurve _ t * F4Chevalley.rootCurve _ (-t⁻¹) * F4Chevalley.rootCurve _ t) * _
  simp only [F4Chevalley.rootCurve, F4Chevalley.integralOperators,
    rootCurveUnit_of_pos r hr, rootCurveUnit_of_neg (-r) hn,
    rootCurveUnit_simple, rootCurveUnit_neg_simple]
  rw [show -(-r) = r from neg_neg r]
  group

private theorem weylWord_neg_route (m : ℕ) (r : F4Chevalley.Root)
    (hr : ¬ typeF4RootPairing_base.IsPos r) (t : CoefficientField m) :
    (weylWord m r t).val =
      rootCurveTitsWord (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-r)).word *
        (weylWord m (-(rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-r)).simple :
          F4Chevalley.Root) t).val *
        (rootCurveTitsWord (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-r)).word)⁻¹ := by
  have hn : typeF4RootPairing_base.IsPos (-r) :=
    (RootPairing.Base.IsPos.neg_iff_not _ r).mpr hr
  change F4Chevalley.rootCurve r t * F4Chevalley.rootCurve (-r) (-t⁻¹) *
    F4Chevalley.rootCurve r t = _ *
      (F4Chevalley.rootCurve _ t * F4Chevalley.rootCurve _ (-t⁻¹) * F4Chevalley.rootCurve _ t) * _
  simp only [F4Chevalley.rootCurve, F4Chevalley.integralOperators,
    rootCurveUnit_of_neg r hr, rootCurveUnit_of_pos (-r) hn, neg_neg,
    rootCurveUnit_simple, rootCurveUnit_neg_simple]
  group

/-- Positive-root coroot words are exact Tits transports of the simple diagonal matrices. -/
theorem torusWord_pos_coe (m : ℕ) (r : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (t : (CoefficientField m)ˣ) :
    (torusWord m r t).val =
      rootCurveTitsWord (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).word *
        diagonalTorusHom m (integralChevalleySimpleCorootParameter
          (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).simple t⁻¹) *
        (rootCurveTitsWord (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).word)⁻¹ := by
  change (weylWord m r t).val * (weylWord m r (-1)).val = _
  rw [weylWord_pos_route m r hr, weylWord_pos_route m r hr]
  rw [← torusWord_simple_coe]
  change _ = _ * ((weylWord m _ t).val * (weylWord m _ (-1)).val) * _
  group

/-- Negative-root words use the same chosen route, with the reversed coroot parameter. -/
theorem torusWord_neg_coe (m : ℕ) (r : F4Chevalley.Root)
    (hr : ¬ typeF4RootPairing_base.IsPos r) (t : (CoefficientField m)ˣ) :
    (torusWord m r t).val =
      rootCurveTitsWord (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-r)).word *
        diagonalTorusHom m (integralChevalleySimpleCorootParameter
          (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-r)).simple t) *
        (rootCurveTitsWord (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-r)).word)⁻¹ := by
  change (weylWord m r t).val * (weylWord m r (-1)).val = _
  rw [weylWord_neg_route m r hr, weylWord_neg_route m r hr]
  rw [← torusWord_neg_simple_coe]
  change _ = _ * ((weylWord m _ t).val * (weylWord m _ (-1)).val) * _
  group

/-- Every coroot word lies in the actual diagonal image inside the split matrix carrier. -/
theorem torusWord_mem_diagonalTorus (m : ℕ) (r : F4Chevalley.Root)
    (t : (CoefficientField m)ˣ) : torusWord m r t ∈ diagonalTorus m := by
  change (torusWord m r t).val ∈ (diagonalTorusHom m).range
  by_cases hr : typeF4RootPairing_base.IsPos r
  · rw [torusWord_pos_coe m r hr]
    exact tits_conj_diagonal_mem m _ _
  · rw [torusWord_neg_coe m r hr]
    exact tits_conj_diagonal_mem m _ _

/-- Simple coroot words already generate every diagonal parameter matrix. -/
theorem diagonalTorusHom_mem_splitTorus_map (m : ℕ) (u : TorusParameter m) :
    diagonalTorusHom m u ∈ (splitTorus m).map (SplitGroup m).subtype := by
  have hs (i : typeF4RootPairing_base.support) (t : (CoefficientField m)ˣ) :
      diagonalTorusHom m (integralChevalleySimpleCorootParameter i t) ∈
        (splitTorus m).map (SplitGroup m).subtype := by
    refine ⟨torusWord m i t⁻¹, Subgroup.subset_closure ⟨i, t⁻¹, rfl⟩, ?_⟩
    change (torusWord m i t⁻¹).val = _
    simpa only [inv_inv] using torusWord_simple_coe m i t⁻¹
  have hp (s : Finset typeF4RootPairing_base.support) :
      diagonalTorusHom m (∏ i ∈ s, integralChevalleySimpleCorootParameter i (u i)) ∈
        (splitTorus m).map (SplitGroup m).subtype := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.prod_empty, map_one]; exact Subgroup.one_mem _
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, map_mul]
      exact Subgroup.mul_mem _ (hs i (u i)) ih
  simpa only [parameter_prod_simple] using hp Finset.univ

/-- The unchanged coroot-word torus equals the diagonal realization for every Ree parameter. -/
theorem splitTorus_eq_diagonalTorus (m : ℕ) : splitTorus m = diagonalTorus m := by
  apply le_antisymm (splitTorus_le_diagonalTorus_of_words m (torusWord_mem_diagonalTorus m))
  intro x hx
  obtain ⟨u, hu⟩ := hx
  obtain ⟨y, hy, he⟩ := diagonalTorusHom_mem_splitTorus_map m u
  have hyx : y = x := Subtype.ext (he.trans hu)
  exact hyx ▸ hy

/-- At the binary endpoint both realizations are the trivial torus. -/
@[simp] theorem diagonalTorus_zero : diagonalTorus 0 = ⊥ := by
  rw [← splitTorus_eq_diagonalTorus, splitTorus_zero]

end ReeF4.Parabolics
