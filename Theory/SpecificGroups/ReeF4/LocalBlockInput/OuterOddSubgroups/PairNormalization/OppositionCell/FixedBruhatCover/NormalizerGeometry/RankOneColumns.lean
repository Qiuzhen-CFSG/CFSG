module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry.Matrices
public import Theory.AlgebraicGroup.Borel.IntegralChevalleyTorusConjugation
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Transport.Curves

/-!
# Root columns of the nonzero rank-one words

The actual word `x_r(t) x_{-r}(-t⁻¹) x_r(t)` permutes the root lines by
nonzero scalars and preserves the Cartan subspace, for every root and every
unit parameter in a Ree coefficient field.

The integral simple Tits lift has signed reflection columns. Specializing
its root and Cartan columns proves the matrix condition for every Tits word.
Diagonal coroot conjugation gives the simple rank-one words at square
parameters; every unit in the finite characteristic-two field is a square.
The integral simple-root exchange also identifies the negative simple word
at parameter one. Finally, the positive and negative canonical root curves
use the same Tits route, so conjugating the entire three-factor word handles
both signs of every root.

Source: the rank-one words and Chevalley relations of GLS3 1.12.1,
`refs/KGroup/GLS3/Chapter1.tex`. This is the root-column calculation used in
Bruhat middle-factor uniqueness (GLS3 1.11.5 and 2.3.5,
`refs/KGroup/GLS3/chapter2.tex`); it assumes no Bruhat decomposition.
The simple square-parameter calculation adapts the diagonal conjugation
argument in `ParabolicAmalgam.OuterLocal.SuzukiCommutators.TorusScaling`.
-/

public section

open scoped Matrix
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
namespace ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
open WordRelations NormalizerGeometry
noncomputable section
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem titsLift_monomial (m : ℕ) (i : typeF4RootPairing_base.support) :
    IsRootMonomial (specializeMatrix (S := CoefficientField m) (titsLift i)) := by
  classical
  refine ⟨typeF4RootPairing.reflectionPerm i, fun _ => 1, ?_, ?_⟩
  · intro a r
    have h := congrFun (titsLift_mulVec_v i r) a
    have hc : titsLift i a (.inr r) =
        if a = .inr (typeF4RootPairing.reflectionPerm i r) then
          (-1 : ℤ) ^ typeF4RootPairing.chainBotCoeff i r else 0 := by
      simp [v, Pi.single_apply] at h
      convert h using 1
    simp only [specializeMatrix, Matrix.map_apply, hc]
    split_ifs <;> simp [CharTwo.neg_eq]
  · intro r c
    have h := congrFun (titsLift_mulVec_u i c) (.inr r)
    have hc : titsLift i (.inr r) (.inl c) = 0 := by
      simpa [u, Pi.single_apply] using h
    simp [specializeMatrix, hc]

private theorem titsUnit_monomial (m : ℕ) (word : List typeF4RootPairing_base.support) :
    IsRootMonomial (titsUnit (S := CoefficientField m) word).val := by
  induction word with
  | nil => simpa using (isRootMonomial_one (C := typeF4RootPairing_base.support)
      (R := F4Chevalley.Root) (K := CoefficientField m))
  | cons i word ih =>
    change IsRootMonomial (specializeMatrix (titsLift i * titsWord word))
    rw [specializeMatrix_mul]
    exact (titsLift_monomial m i).mul ih

private abbrev diag (m : ℕ) (i : typeF4RootPairing_base.support)
    (u : (CoefficientField m)ˣ) :=
  integralChevalleyTorusElement (P := typeF4RootPairing)
    (integralChevalleySimpleCorootParameter i u)

private theorem diag_monomial (m : ℕ) (i : typeF4RootPairing_base.support)
    (u : (CoefficientField m)ˣ) : IsRootMonomial (diag m i u).val := by
  classical
  refine ⟨Equiv.refl _, fun r => chevalleyBasisTorusUnit (P := typeF4RootPairing)
    (integralChevalleySimpleCorootParameter i u) (.inr r), ?_, ?_⟩
  · intro a r
    simp only [diag, integralChevalleyTorusElement, Matrix.diagonal_apply,
      Equiv.refl_apply]
    by_cases h : a = .inr r
    · subst a; simp
    · simp [h]
  · intro r c
    simp [diag, integralChevalleyTorusElement]

private theorem diag_root (m : ℕ) (i : typeF4RootPairing_base.support)
    (u : (CoefficientField m)ˣ) (r : F4Chevalley.Root) (t : CoefficientField m) :
    (diag m i u)⁻¹ * F4Chevalley.rootCurve r t * diag m i u =
      F4Chevalley.rootCurve r
        (((u ^ typeF4RootPairing.pairingIn ℤ r i :
          (CoefficientField m)ˣ) : CoefficientField m) * t) := by
  exact integralChevalleyRootCurve_simpleCoroot_conjugation i u r t

private theorem rankOne_simple_one (m : ℕ) (i : typeF4RootPairing_base.support) :
    (rankOneRepresentative m i.val 1).val = titsUnit [i] := by
  rw [titsUnit_cons, titsUnit_nil, mul_one]
  rfl

private theorem specialize_e (m : ℕ) (i : typeF4RootPairing_base.support) (t : ℤ) :
    specializeMatrix (S := CoefficientField m) (eUnipotent i t) =
      positiveMatrix i (t : CoefficientField m) := by
  ext j k
  simp only [specializeMatrix, eUnipotent, positiveMatrix_formula, Matrix.map_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Int.coe_castRingHom,
    Int.cast_add, Int.cast_mul, Int.cast_pow]
  simp [Matrix.one_apply]

private theorem specialize_f (m : ℕ) (i : typeF4RootPairing_base.support) (t : ℤ) :
    specializeMatrix (S := CoefficientField m) (fUnipotent i t) =
      negativeMatrix i (t : CoefficientField m) := by
  ext j k
  simp only [specializeMatrix, fUnipotent, negativeMatrix_formula, Matrix.map_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Int.coe_castRingHom,
    Int.cast_add, Int.cast_mul, Int.cast_pow]
  simp [Matrix.one_apply]

private theorem titsUnit_simple_mul_positive (m : ℕ)
    (i : typeF4RootPairing_base.support) :
    titsUnit [i] * F4Chevalley.rootCurve i.val (1 : CoefficientField m) =
      F4Chevalley.rootCurve (-i.val) 1 * titsUnit [i] := by
  change titsUnit [i] * rootCurveUnit integralChevalleyRootOperators i.val _ =
    rootCurveUnit integralChevalleyRootOperators (-i.val) _ * titsUnit [i]
  rw [rootCurveUnit_simple, rootCurveUnit_neg_simple]
  apply Units.ext
  change specializeMatrix (titsWord [i]) * positiveMatrix i 1 =
    negativeMatrix i 1 * specializeMatrix (titsWord [i])
  simp only [titsWord, mul_one]
  have he := congrArg (specializeMatrix (S := CoefficientField m))
    (titsLift_mul_eUnipotent i 1)
  rw [specializeMatrix_mul, specializeMatrix_mul, specialize_e, specialize_f] at he
  simpa only [Int.cast_one, Int.cast_neg, CharTwo.neg_eq] using he

private theorem rankOne_neg_simple_one (m : ℕ) (i : typeF4RootPairing_base.support) :
    (rankOneRepresentative m (-i.val) 1).val = titsUnit [i] := by
  have h := titsUnit_simple_mul_positive m i
  rw [titsUnit_cons, titsUnit_nil, mul_one] at h
  simp only [CharTwo.neg_eq] at h
  have he : F4Chevalley.rootCurve i.val (1 : CoefficientField m) *
      F4Chevalley.rootCurve i.val 1 = 1 := by
    rw [← F4Chevalley.rootCurve_add]
    simp [CharTwo.add_self_eq_zero]
  have hh := congrArg (fun x => x * F4Chevalley.rootCurve i.val 1) h
  simp only [mul_assoc, he, mul_one] at hh
  rw [titsUnit_cons, titsUnit_nil, mul_one]
  change F4Chevalley.rootCurve (-i.val) _ * F4Chevalley.rootCurve (-(-i.val)) _ *
    F4Chevalley.rootCurve (-i.val) _ = _
  simpa only [neg_neg, Units.val_one, inv_one, CharTwo.neg_eq, mul_assoc] using hh.symm

private theorem rankOne_coroot (m : ℕ) (i : typeF4RootPairing_base.support)
    (r : F4Chevalley.Root) (u : (CoefficientField m)ˣ) :
    (rankOneRepresentative m r (u ^ typeF4RootPairing.pairingIn ℤ r i)).val =
      (diag m i u)⁻¹ * (rankOneRepresentative m r 1).val * diag m i u := by
  change F4Chevalley.rootCurve _ _ * F4Chevalley.rootCurve _ _ *
    F4Chevalley.rootCurve _ _ =
    (diag m i u)⁻¹ * (F4Chevalley.rootCurve r 1 * F4Chevalley.rootCurve (-r) (-1) *
      F4Chevalley.rootCurve r 1) * diag m i u
  symm
  calc
    _ = ((diag m i u)⁻¹ * F4Chevalley.rootCurve r 1 * diag m i u) *
        ((diag m i u)⁻¹ * F4Chevalley.rootCurve (-r) (-1) * diag m i u) *
        ((diag m i u)⁻¹ * F4Chevalley.rootCurve r 1 * diag m i u) := by group
    _ = _ := by simp [diag_root, RootPairing.indexNeg_neg]

private theorem unit_square_root (m : ℕ) (t : (CoefficientField m)ˣ) :
    ∃ u : (CoefficientField m)ˣ, u ^ 2 = t := by
  obtain ⟨a, ha⟩ := isSquare_of_charTwo' t.val
  have ha0 : a ≠ 0 := by
    intro h
    exact t.ne_zero (ha.trans (by simp [h]))
  refine ⟨Units.mk0 a ha0, ?_⟩
  apply Units.ext
  simpa [pow_two] using ha.symm

private theorem rankOne_simple_monomial (m : ℕ) (i : typeF4RootPairing_base.support)
    (t : (CoefficientField m)ˣ) :
    IsRootMonomial (rankOneRepresentative m i.val t).val.val := by
  obtain ⟨u, rfl⟩ := unit_square_root m t
  have h := rankOne_coroot m i i.val u
  simp only [RootPairing.pairingIn_same, zpow_ofNat] at h
  rw [h, rankOne_simple_one, Units.val_mul, Units.val_mul]
  exact ((diag_monomial m i u).inv.mul (titsUnit_monomial m [i])).mul
    (diag_monomial m i u)

private theorem rankOne_neg_simple_monomial (m : ℕ) (i : typeF4RootPairing_base.support)
    (t : (CoefficientField m)ˣ) :
    IsRootMonomial (rankOneRepresentative m (-i.val) t).val.val := by
  obtain ⟨u, rfl⟩ := unit_square_root m t
  have h := rankOne_coroot m i (-i.val) u⁻¹
  have hp : typeF4RootPairing.pairingIn ℤ (-i.val) i = -2 := by
    simp [RootPairing.indexNeg_neg]
  simp only [hp, zpow_neg, zpow_ofNat, inv_pow, inv_inv] at h
  rw [h, rankOne_neg_simple_one, Units.val_mul, Units.val_mul]
  exact ((diag_monomial m i u⁻¹).inv.mul (titsUnit_monomial m [i])).mul
    (diag_monomial m i u⁻¹)

private theorem rankOne_pos_route (m : ℕ) (r : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (t : (CoefficientField m)ˣ) :
    let D := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
    (rankOneRepresentative m r t).val =
      titsUnit D.word * (rankOneRepresentative m D.simple.val t).val *
        (titsUnit D.word)⁻¹ := by
  dsimp only
  change F4Chevalley.rootCurve r _ * F4Chevalley.rootCurve (-r) _ *
    F4Chevalley.rootCurve r _ = _
  rw [rootCurve_of_pos_route r hr, rootCurve_neg_of_pos_route r hr]
  change (_ * _ * _⁻¹) * (_ * _ * _⁻¹) * (_ * _ * _⁻¹) =
    _ * (_ * _ * _) * _⁻¹
  group
  rfl

private theorem rankOne_neg_pos_route (m : ℕ) (r : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (t : (CoefficientField m)ˣ) :
    let D := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
    (rankOneRepresentative m (-r) t).val =
      titsUnit D.word * (rankOneRepresentative m (-D.simple.val) t).val *
        (titsUnit D.word)⁻¹ := by
  dsimp only
  change F4Chevalley.rootCurve (-r) _ * F4Chevalley.rootCurve (-(-r)) _ *
    F4Chevalley.rootCurve (-r) _ = _
  rw [neg_neg, rootCurve_neg_of_pos_route r hr, rootCurve_of_pos_route r hr]
  change (_ * _ * _⁻¹) * (_ * _ * _⁻¹) * (_ * _ * _⁻¹) =
    _ * (_ * F4Chevalley.rootCurve (-(-_)) _ * _) * _⁻¹
  rw [neg_neg]
  group
  rfl

/-- Every nonzero rank-one word has monomial root columns and preserves the
Cartan subspace. This holds also for the smallest coefficient field. -/
theorem rankOneRepresentative_isRootMonomial (m : ℕ) (r : F4Chevalley.Root)
    (t : (CoefficientField m)ˣ) :
    IsRootMonomial (rankOneRepresentative m r t).val.val := by
  by_cases hr : typeF4RootPairing_base.IsPos r
  · rw [rankOne_pos_route m r hr t, Units.val_mul, Units.val_mul]
    exact ((titsUnit_monomial m _).mul (rankOne_simple_monomial m _ t)).mul
      (titsUnit_monomial m _).inv
  · have hp := (RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base r).mpr hr
    have h := rankOne_neg_pos_route m (-r) hp t
    rw [neg_neg] at h
    rw [h, Units.val_mul, Units.val_mul]
    exact ((titsUnit_monomial m _).mul (rankOne_neg_simple_monomial m _ t)).mul
      (titsUnit_monomial m _).inv

end
end ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
