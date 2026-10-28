module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootHigher.IntegralReduction

/-!
# Integral comparison of actual root operators with arbitrary Weyl routes

A positive-source Tits route to any F4 root gives its actual canonical
integral operator up to sign. For negative roots, append the source simple
reflection to the canonical route of the opposite root; conjugation changes
`e` into `-f`. The sign comparison in `RouteComparison` then applies.
Concatenation gives integral Weyl covariance, again up to sign.

These lemmas retain the signs before characteristic-two specialization and
connect convenient routes to the actual operators in the quadratic problem.
They use `IntegralAllRootOperators` and the integral primitivity and
multiplicity-one comparison of `Intertwining.Transport.RouteComparison`.
-/

public section

open scoped Matrix
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
noncomputable section

/-- An arbitrary positive-source route yields the actual integral operator up to sign. -/
lemma integralRootOperator_eq_sign_transport (r : typeF4Roots)
    (w : List typeF4RootPairing_base.support) (j : typeF4RootPairing_base.support)
    (hw : reflectionWord (P := typeF4RootPairing) w j = r) :
    ∃ ε : ℤ, ε ^ 2 = 1 ∧ F4Chevalley.integralOperators.rootOperator r =
      ε • transportedMatrix w (eMatrix (P := typeF4RootPairing) j) := by
  let := typeF4RootPairing.indexNeg
  change ∃ ε : ℤ, ε ^ 2 = 1 ∧
    rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) r = _
  by_cases hr : typeF4RootPairing_base.IsPos r
  · rw [rootOperator_of_pos r hr]
    obtain ⟨ε, hε, h⟩ := RouteComparison.transported_eDividedPower_eq_sign_smul
      (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).word w
      (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).simple j
      ((rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).target.trans hw.symm)
    exact ⟨ε, hε, by simpa only [eDividedPower_one, pow_one] using h 1⟩
  · have hn : typeF4RootPairing_base.IsPos (-r) :=
      (RootPairing.Base.IsPos.neg_iff_not _ _).mpr hr
    have he := rootOperator_neg_of_pos (P := typeF4RootPairing)
      (b := typeF4RootPairing_base) (-r) hn
    simp only [neg_neg] at he
    rw [he]
    let z := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-r)
    have hz : reflectionWord (P := typeF4RootPairing) (z.word ++ [z.simple]) z.simple =
        reflectionWord w j := by
      rw [RouteComparison.reflectionWord_append_simple_self, z.target, neg_neg, hw]
    obtain ⟨ε, hε, h⟩ := RouteComparison.transported_eDividedPower_eq_sign_smul
      (z.word ++ [z.simple]) w z.simple j hz
    have h1 := h 1
    simp only [eDividedPower_one, pow_one,
      RouteComparison.transportedMatrix_append_simple_eMatrix] at h1
    refine ⟨-ε, by simpa only [neg_sq] using hε, ?_⟩
    have h2 := congrArg Neg.neg h1
    simpa only [neg_neg, neg_smul] using h2

private lemma reflectionWord_append (w z : List typeF4RootPairing_base.support)
    (r : typeF4Roots) :
    reflectionWord (P := typeF4RootPairing) (w ++ z) r =
      reflectionWord w (reflectionWord z r) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.cons_append, reflectionWord, ih]

private lemma titsWordInv_append (w z : List typeF4RootPairing_base.support) :
    titsWordInv (P := typeF4RootPairing) (w ++ z) = titsWordInv z * titsWordInv w := by
  induction w with
  | nil => simp
  | cons i w ih => simp [ih, mul_assoc]

/-- The actual integral root operators are Weyl covariant up to sign. -/
lemma integralRootOperator_reflectionWord (w : List typeF4RootPairing_base.support)
    (r : typeF4Roots) :
    ∃ ε : ℤ, ε ^ 2 = 1 ∧
      F4Chevalley.integralOperators.rootOperator (reflectionWord (P := typeF4RootPairing) w r) =
        ε • transportedMatrix w (F4Chevalley.integralOperators.rootOperator r) := by
  let z := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
  have hwz : reflectionWord (P := typeF4RootPairing) (w ++ z.word) z.simple =
      reflectionWord w r := by rw [reflectionWord_append, z.target]
  obtain ⟨ε, hε, he⟩ := integralRootOperator_eq_sign_transport _ (w ++ z.word) z.simple hwz
  obtain ⟨δ, hδ, hd⟩ := integralRootOperator_eq_sign_transport r z.word z.simple z.target
  refine ⟨ε * δ, by rw [mul_pow, hε, hδ, one_mul], ?_⟩
  rw [he, hd]
  simp only [transportedMatrix, titsWord_append, titsWordInv_append,
    Matrix.mul_smul, Matrix.smul_mul, mul_assoc, smul_smul]
  rw [← pow_two δ, hδ, mul_one]
end
end ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
