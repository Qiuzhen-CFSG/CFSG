module

public import Theory.AlgebraicGroup.RootSystems.IntegralRootCurveSimpleGeneration
public import Theory.AlgebraicGroup.RootSystems.GeckIrreducibleRationalRootspaceOne
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Group.Int.Units

/-!
# Comparison of positive Geck routes in characteristic two

Equal root endpoints put the rational operators in the same one-dimensional
root space. Undoing each integral Tits word exhibits a primitive coefficient,
so the proportionality scalar is an integral sign. Factorial cancellation over
ℤ compares the divided powers before specialization; the sign then disappears
in characteristic two. No choice of canonical route needs to be invariant.

The primitivity and factorial arguments are adapted from the generic portion
of `Theory/SpecificGroups/ReeF4/ExceptionalEndomorphism/WordRelations/
Intertwining/Transport/RouteComparison.lean` in this repository.
Source: Geck's integral construction; GLS3 §§1.12 and 2.3–2.4.
-/

public section
namespace Triality.Standard.PositiveCoordinates.GraphFieldProof
variable {ι : Type*}
private lemma map_conjugating_smul [Fintype ι]
    (A B U V : Matrix ι ι ℤ) (q : ℚ)
    (h : A.map (Int.castRingHom ℚ) = q • B.map (Int.castRingHom ℚ)) :
    (U * A * V).map (Int.castRingHom ℚ) =
      q • (U * B * V).map (Int.castRingHom ℚ) := by
  simp only [Matrix.map_mul, h, Matrix.mul_smul, Matrix.smul_mul]

/-- Integral coordinate functionals taking value `1` force a rational comparison
scalar to be an integral sign. In applications, `U, V` and `W, X` undo the
two Tits conjugations. -/
private theorem eq_sign_smul_of_rat_proportional [Fintype ι]
    (A B U V W X : Matrix ι ι ℤ) (a b c d : ι)
    (hA : (U * A * V) a b = 1) (hB : (W * B * X) c d = 1)
    (q : ℚ) (hq : A.map (Int.castRingHom ℚ) = q • B.map (Int.castRingHom ℚ)) :
    ∃ ε : ℤ, ε ^ 2 = 1 ∧ A = ε • B := by
  let ε : ℤ := (W * A * X) c d
  have hε : (ε : ℚ) = q := by
    have h := congrFun (congrFun (map_conjugating_smul A B W X q hq) c) d
    change (↑((W * A * X) c d) : ℚ) = q * ↑((W * B * X) c d) at h
    simpa [hB, ε] using h
  have hAB : A = ε • B := by
    ext x y
    apply Int.cast_injective (α := ℚ)
    have h := congrFun (congrFun hq x) y
    change (↑(A x y) : ℚ) = q * ↑(B x y) at h
    change (↑(A x y) : ℚ) = ↑(ε * B x y)
    rw [Int.cast_mul, hε]
    exact h
  have hunit : ε * (U * B * V) a b = 1 := by
    rw [hAB, Matrix.mul_smul, Matrix.smul_mul] at hA
    exact hA
  refine ⟨ε, ?_, hAB⟩
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hunit with h | h <;> simp [h]

/-- A scalar comparison of integral operators determines their divided powers.
The factorial is cancelled over the integers, before any specialization. -/
private theorem dividedPower_eq_sign_smul [Fintype ι] [DecidableEq ι]
    (A B D E : Matrix ι ι ℤ) (n : ℕ) (ε : ℤ)
    (hA : A ^ n = n.factorial • D) (hB : B ^ n = n.factorial • E)
    (hAB : A = ε • B) : D = ε ^ n • E := by
  have h : n.factorial • D = n.factorial • (ε ^ n • E) := by
    rw [← hA, hAB, smul_pow, hB, smul_comm]
  ext x y
  have hxy := congrFun (congrFun h x) y
  simp only [Matrix.smul_apply, nsmul_eq_mul, smul_eq_mul] at hxy ⊢
  exact mul_left_cancel₀ (by exact_mod_cast n.factorial_ne_zero) hxy

/-- Powers of an integral sign disappear over every ring of characteristic two. -/
private theorem map_eq_of_sign_smul {S : Type*} [CommRing S] [CharP S 2]
    (A B : Matrix ι ι ℤ) (ε : ℤ) (n : ℕ)
    (hε : ε ^ 2 = 1) (hAB : A = ε ^ n • B) :
    A.map (Int.castRingHom S) = B.map (Int.castRingHom S) := by
  have he : (ε : S) = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one (by simpa [pow_two] using hε) with h | h
    · simp [h]
    · simp [h, CharTwo.neg_eq]
  rw [hAB]
  ext x y
  change (↑(ε ^ n * B x y) : S) = ↑(B x y)
  rw [Int.cast_mul, Int.cast_pow, he, one_pow, one_mul]

section Integral

open RootPairing.IntegralGeckConstruction

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

private lemma undo_transportedMatrix (word : List b.support)
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    titsWordInv word * transportedMatrix word A * titsWord word = A := by
  rw [transportedMatrix]
  calc
    titsWordInv word * (titsWord word * A * titsWordInv word) * titsWord word =
        (titsWordInv word * titsWord word) * A *
          (titsWordInv word * titsWord word) := by noncomm_ring
    _ = A := by rw [titsWord_inv_mul, Matrix.one_mul, Matrix.mul_one]

private lemma transported_eMatrix_primitive (word : List b.support) (i : b.support) :
    letI := P.indexNeg
    (titsWordInv word * transportedMatrix word (eMatrix i) * titsWord word)
      (Sum.inl i) (Sum.inr (-i : ι)) = 1 := by
  letI := P.indexNeg
  rw [undo_transportedMatrix]
  simp [eMatrix]

/-- Rationally proportional positive simple operators transported along arbitrary words
agree up to an integral sign. Primitivity is measured after undoing each transport. -/
private theorem transported_eMatrix_eq_sign_smul_of_rat_proportional
    (w z : List b.support) (i j : b.support) (q : ℚ)
    (hq : (titsConjugate w (eMatrix i)).map (algebraMap ℤ ℚ) =
      q • (titsConjugate z (eMatrix j)).map (algebraMap ℤ ℚ)) :
    ∃ ε : ℤ, ε ^ 2 = 1 ∧
      transportedMatrix w (eMatrix i) = ε • transportedMatrix z (eMatrix j) := by
  letI := P.indexNeg
  exact eq_sign_smul_of_rat_proportional
    (transportedMatrix w (eMatrix i)) (transportedMatrix z (eMatrix j))
    (titsWordInv w) (titsWord w) (titsWordInv z) (titsWord z)
    (Sum.inl i) (Sum.inr (-i : ι)) (Sum.inl j) (Sum.inr (-j : ι))
    (transported_eMatrix_primitive w i) (transported_eMatrix_primitive z j) q hq

/-- One integral sign simultaneously compares every positive divided power.
The factorials are cancelled over the integers before specialization. -/
private theorem transported_eDividedPower_eq_sign_smul_of_rat_proportional
    (w z : List b.support) (i j : b.support) (q : ℚ)
    (hq : (titsConjugate w (eMatrix i)).map (algebraMap ℤ ℚ) =
      q • (titsConjugate z (eMatrix j)).map (algebraMap ℤ ℚ)) :
    ∃ ε : ℤ, ε ^ 2 = 1 ∧ ∀ n : ℕ,
      transportedMatrix w (eDividedPower i n) =
        ε ^ n • transportedMatrix z (eDividedPower j n) := by
  obtain ⟨ε, hε, h⟩ := transported_eMatrix_eq_sign_smul_of_rat_proportional w z i j q hq
  refine ⟨ε, hε, fun n => ?_⟩
  apply dividedPower_eq_sign_smul _ _ _ _ n ε _ _ h
  · rw [← transportedMatrix_pow, eMatrix_pow_eq_factorial_smul, transportedMatrix_smul]
  · rw [← transportedMatrix_pow, eMatrix_pow_eq_factorial_smul, transportedMatrix_smul]

variable [P.IsRootSystem] [P.IsIrreducible]

/-- Positive simple routes with the same endpoint have identical specialized
divided powers in characteristic two, regardless of the canonical route choices. -/
theorem specialize_route_eq {S : Type*} [CommRing S] [CharP S 2]
    (w z : List b.support) (i j : b.support) (n : ℕ)
    (hroot : reflectionWord w (i : ι) = reflectionWord z (j : ι)) :
    specializeMatrix (S := S) (transportedMatrix w (eDividedPower i n)) =
      specializeMatrix (S := S) (transportedMatrix z (eDividedPower j n)) := by
  obtain ⟨q, hq⟩ := exists_rat_smul_titsConjugate_of_reflectionWord_eq w z i j hroot
  obtain ⟨ε, hε, h⟩ := transported_eDividedPower_eq_sign_smul_of_rat_proportional w z i j q hq
  exact map_eq_of_sign_smul _ _ ε n hε (h n)

end Integral
end Triality.Standard.PositiveCoordinates.GraphFieldProof
