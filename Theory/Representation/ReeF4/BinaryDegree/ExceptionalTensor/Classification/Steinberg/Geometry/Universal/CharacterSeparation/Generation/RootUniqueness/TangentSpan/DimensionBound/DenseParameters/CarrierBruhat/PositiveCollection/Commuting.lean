module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.NoRootSums
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Simple.DividedPowers

/-!
# Commuting positive F4 root matrices

If the sum of two positive roots is absent, their integral operators commute.
Transport the first root to a simple root and compare the second canonical
route with a route through that same Weyl word. Integral route comparison
contributes only a scalar sign, so the simple-root absent-weight calculation
applies. Cancel factorials over the integers to obtain commutation of every
pair of divided powers, and then specialize the quadratic root curves.

This is the empty-correction branch for the literal carrier over any field.
Adapted from `SplitCoordinates.MatrixExchanges.Commuting`; the original
finite-support wrappers are not imported.

Adapted from the corresponding `ReeF4.Parabolics.RadicalCoordinates` proof,
with its finite-carrier import removed.

Source: the Chevalley root collection underlying Aschbacher–Smith,
F.1.12(I)(5), printed p.263 of `refs/quasithin.pdf`; integral Geck operators
and Tits route comparison are the existing representation used here.
-/

public section

open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped Matrix
namespace Theory.AlgebraicGroup.F4Chevalley.DenseParameters.CarrierBruhat.CollectionMatrices
noncomputable section

private lemma reflectionWord_append (w z : List typeF4RootPairing_base.support)
    (r : F4Chevalley.Root) :
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

private lemma transportedMatrix_append (w z : List typeF4RootPairing_base.support)
    (A : F4Chevalley.IntegralMatrix) :
    transportedMatrix (P := typeF4RootPairing) (w ++ z) A =
      transportedMatrix w (transportedMatrix z A) := by
  simp only [transportedMatrix, titsWord_append, titsWordInv_append, mul_assoc]

/-- The integral operators commute when the sum of two positive roots is absent. -/
theorem integralOperators_commute_of_no_sum (r s : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (hs : typeF4RootPairing_base.IsPos s)
    (h0 : typeF4RootPairing.root r + typeF4RootPairing.root s ≠ 0)
    (hsum : typeF4RootPairing.root r + typeF4RootPairing.root s ∉
      Set.range typeF4RootPairing.root) :
    Commute (F4Chevalley.integralOperators.rootOperator r)
      (F4Chevalley.integralOperators.rootOperator s) := by
  classical
  let z := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
  let e := typeF4RootPairing.weylGroupToPerm (typeF4RootPairing_base.wordProd z.word)
  let t := e.symm s
  have hts : reflectionWord (P := typeF4RootPairing) z.word t = s := by
    rw [reflectionWord_eq_weylGroupToPerm]
    exact e.apply_symm_apply s
  let v := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) t
  have h0' : typeF4RootPairing.root z.simple + typeF4RootPairing.root t ≠ 0 := by
    intro he
    apply h0
    have he' := congrArg (fun x => typeF4RootPairing_base.wordProd z.word • x) he
    rw [smul_add, smul_zero, ← root_reflectionWord, ← root_reflectionWord,
      z.target, hts] at he'
    exact he'
  have hs' : typeF4RootPairing.root z.simple + typeF4RootPairing.root t ∉
      Set.range typeF4RootPairing.root := by
    rintro ⟨u, hu⟩
    apply hsum
    refine ⟨reflectionWord (P := typeF4RootPairing) z.word u, ?_⟩
    rw [root_reflectionWord, hu, smul_add, ← root_reflectionWord,
      ← root_reflectionWord, z.target, hts]
  have hc : Commute (eMatrix (P := typeF4RootPairing) z.simple)
      (transportedMatrix v.word (eMatrix v.simple)) := by
    have h := integral_commutator_zero (P := typeF4RootPairing)
      z.simple v.simple v.word (by simpa only [v.target] using h0')
      (by simpa only [v.target] using hs')
    simpa only [sub_eq_zero, titsConjugate_apply, transportedMatrix, Commute, SemiconjBy] using h
  let u := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) s
  have he : reflectionWord (P := typeF4RootPairing) u.word u.simple =
      reflectionWord (z.word ++ v.word) v.simple := by
    rw [u.target, reflectionWord_append, v.target, hts]
  obtain ⟨c, _, hc'⟩ := ReeF4.WordRelations.RouteComparison.transported_eDividedPower_eq_sign_smul
    u.word (z.word ++ v.word) u.simple v.simple he
  have hcop := hc' 1
  simp only [eDividedPower_one, pow_one, transportedMatrix_append] at hcop
  change Commute (rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) r)
    (rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) s)
  rw [rootOperator_of_pos r hr, rootOperator_of_pos s hs]
  change Commute (transportedMatrix z.word (eMatrix z.simple))
    (transportedMatrix u.word (eMatrix u.simple))
  rw [hcop]
  apply Commute.smul_right
  change _ * _ = _ * _
  rw [← transportedMatrix_mul, ← transportedMatrix_mul, hc.eq]

private lemma dividedPowers_commute (r s : F4Chevalley.Root)
    (h : Commute (F4Chevalley.integralOperators.rootOperator r)
      (F4Chevalley.integralOperators.rootOperator s)) (i j : ℕ) :
    Commute (F4Chevalley.integralOperators.rootDividedPower r i)
      (F4Chevalley.integralOperators.rootDividedPower s j) := by
  have hh := (h.pow_pow i j).eq
  rw [F4Chevalley.operator_pow_eq_factorial_smul,
    F4Chevalley.operator_pow_eq_factorial_smul] at hh
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul] at hh
  rw [Nat.mul_comm j.factorial i.factorial] at hh
  ext x y
  exact nsmul_right_injective (Nat.mul_ne_zero (Nat.factorial_ne_zero i)
    (Nat.factorial_ne_zero j)) (congrFun₂ hh x y)

/-- Integral operator commutation implies curve commutation in every characteristic;
the factorials are cancelled before scalar specialization. -/
theorem rootCurve_commute_of_integralOperators {K : Type*} [CommRing K]
    (r s : F4Chevalley.Root)
    (h : Commute (F4Chevalley.integralOperators.rootOperator r)
      (F4Chevalley.integralOperators.rootOperator s)) (a b : K) :
    Commute (F4Chevalley.rootCurve r a) (F4Chevalley.rootCurve s b) := by
  have hc (i j : ℕ) :
      Commute (specializeMatrix (S := K) (F4Chevalley.integralOperators.rootDividedPower r i))
        (specializeMatrix (S := K) (F4Chevalley.integralOperators.rootDividedPower s j)) :=
    (dividedPowers_commute r s h i j).map (Int.castRingHom K).mapMatrix
  have hab (i j : ℕ) (x y : K) :
      Commute (x • specializeMatrix (S := K) (F4Chevalley.integralOperators.rootDividedPower r i))
        (y • specializeMatrix (S := K) (F4Chevalley.integralOperators.rootDividedPower s j)) :=
    ((hc i j).smul_left x).smul_right y
  apply Units.ext
  change _ * _ = _ * _
  rw [ReeF4.WordRelations.rootCurve_quadratic, ReeF4.WordRelations.rootCurve_quadratic]
  exact (Commute.add_left
    (Commute.add_left (Commute.one_left _)
      (((Commute.one_right _).add_right (hab 1 1 a b)).add_right (hab 1 2 a (b ^ 2))))
    (((Commute.one_right _).add_right (hab 2 1 (a ^ 2) b)).add_right
      (hab 2 2 (a ^ 2) (b ^ 2)))).eq

end
end Theory.AlgebraicGroup.F4Chevalley.DenseParameters.CarrierBruhat.CollectionMatrices
