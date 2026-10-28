module

public import Mathlib.LinearAlgebra.Matrix.Integer
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Group.Int.Units
public import Theory.AlgebraicGroup.Borel.IntegralChevalleyRootCurves
public import Theory.AlgebraicGroup.RootSystems.F4RootPairing
public import Theory.AlgebraicGroup.RootSystems.GeckIrreducibleRationalRootspaceOne

/-!
# Integral matrix comparisons for F4 root routes

These matrix lemmas provide the primitivity and divided-power steps of the
comparison of integral Geck operators along different root routes. If two
integral matrices are rationally proportional and each admits an integral
coordinate functional with value `1`, the proportionality factor is an
integral sign. Their divided powers then differ by powers of that sign and
become equal in characteristic two.

The coordinate functionals are expressed as entries of `U * A * V`. For the
actual Geck operators we undo the integral Tits conjugations and read the
primitive simple-operator coefficient. The negative case is reduced to the
positive case by appending the source simple reflection: comparison of the
cubic unipotent polynomials at `1`, `-1`, and `2` proves the matrix identity
`n_i e_i n_i⁻¹ = -f_i`. The appended routes reach the opposite roots.

For the actual F4 root pairing, equal endpoints of arbitrary reflection words
give rational proportionality by
`exists_rat_smul_titsConjugate_of_reflectionWord_eq` from
`GeckIrreducibleRationalRootspaceOne`. Thus both positive and negative divided
powers are independent of the chosen route after specialization to any
commutative ring of characteristic two. The factorial identities and the simple-reflection exchange formula
come from Geck's integral construction in `IntegralGeckConstruction`.
-/

public section

namespace ReeF4.WordRelations.RouteComparison

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
theorem eq_sign_smul_of_rat_proportional [Fintype ι]
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
theorem dividedPower_eq_sign_smul [Fintype ι] [DecidableEq ι]
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
theorem map_eq_of_sign_smul {S : Type*} [CommRing S] [CharP S 2]
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

/-- The complete matrix criterion for equality of specialized divided powers.
Its hypotheses separate rational root-space proportionality, integral
primitivity, and the factorial identities of the actual operators. -/
theorem map_dividedPower_eq_of_rat_proportional [Fintype ι] [DecidableEq ι]
    {S : Type*} [CommRing S] [CharP S 2]
    (A B D E U V W X : Matrix ι ι ℤ) (a b c d : ι) (n : ℕ)
    (hA : (U * A * V) a b = 1) (hB : (W * B * X) c d = 1)
    (hD : A ^ n = n.factorial • D) (hE : B ^ n = n.factorial • E)
    (q : ℚ) (hq : A.map (Int.castRingHom ℚ) = q • B.map (Int.castRingHom ℚ)) :
    D.map (Int.castRingHom S) = E.map (Int.castRingHom S) := by
  obtain ⟨ε, hε, hAB⟩ := eq_sign_smul_of_rat_proportional A B U V W X a b c d hA hB q hq
  exact map_eq_of_sign_smul D E ε n hε
    (dividedPower_eq_sign_smul A B D E n ε hD hE hAB)

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
theorem transported_eMatrix_eq_sign_smul_of_rat_proportional
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

/-- The linear coefficient of the simple-root exchange formula: a Tits lift
exchanges the positive and negative infinitesimal operators with a minus sign. -/
theorem titsLift_mul_eMatrix_neg (i : b.support) :
    titsLift i * eMatrix i = -(fMatrix i * titsLift i) := by
  ext x y
  have h1 := congrFun (congrFun (titsLift_mul_eUnipotent i 1) x) y
  have hm1 := congrFun (congrFun (titsLift_mul_eUnipotent i (-1)) x) y
  have h2 := congrFun (congrFun (titsLift_mul_eUnipotent i 2) x) y
  simp only [eUnipotent, fUnipotent, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
    Matrix.smul_apply, eDividedPower_one, fDividedPower_one] at h1 hm1 h2
  norm_num at h1 hm1 h2
  change _ = -((fMatrix i * titsLift i) x y)
  omega

/-- Conjugation by the simple Tits lift sends `e_i` to `-f_i` over the integers. -/
theorem titsLift_conj_eMatrix_neg (i : b.support) :
    titsLift i * eMatrix i * titsLiftInv i = -fMatrix i := by
  rw [titsLift_mul_eMatrix_neg, neg_mul, mul_assoc, titsLift_mul_inv, mul_one]

private lemma titsWordInv_append_route (w z : List b.support) :
    titsWordInv (w ++ z) = titsWordInv z * titsWordInv w := by
  induction w with
  | nil => simp
  | cons i w ih => simp [ih, mul_assoc]

private lemma transportedMatrix_append_route (w z : List b.support)
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    transportedMatrix (w ++ z) A = transportedMatrix w (transportedMatrix z A) := by
  simp only [transportedMatrix, titsWord_append, titsWordInv_append_route, mul_assoc]

/-- Appending the source simple reflection converts positive operator transport
to the negative operator along the original route, with a minus sign. -/
theorem transportedMatrix_append_simple_eMatrix (w : List b.support) (i : b.support) :
    transportedMatrix (w ++ [i]) (eMatrix i) = -transportedMatrix w (fMatrix i) := by
  rw [transportedMatrix_append_route]
  have hi : transportedMatrix [i] (eMatrix i) = -fMatrix i := by
    simpa only [transportedMatrix, titsWord, titsWordInv_cons, titsWordInv_nil,
      mul_one, one_mul] using titsLift_conj_eMatrix_neg i
  rw [hi]
  simp only [transportedMatrix, mul_neg, neg_mul]

private lemma reflectionWord_append_route (w z : List b.support) (r : ι) :
    reflectionWord (w ++ z) r = reflectionWord w (reflectionWord z r) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.cons_append, reflectionWord, ih]

/-- Appending the source simple reflection makes the route reach the opposite root. -/
theorem reflectionWord_append_simple_self (w : List b.support) (i : b.support) :
    letI := P.indexNeg
    reflectionWord (w ++ [i]) (i : ι) = -reflectionWord w (i : ι) := by
  letI := P.indexNeg
  rw [reflectionWord_append_route]
  change reflectionWord w (-(i : ι)) = _
  exact reflectionWord_neg w i

/-- Negative operator comparison follows from positive rational comparison along
the routes with their source simple reflections appended. -/
theorem transported_fMatrix_eq_sign_smul_of_rat_proportional
    (w z : List b.support) (i j : b.support) (q : ℚ)
    (hq : (titsConjugate (w ++ [i]) (eMatrix i)).map (algebraMap ℤ ℚ) =
      q • (titsConjugate (z ++ [j]) (eMatrix j)).map (algebraMap ℤ ℚ)) :
    ∃ ε : ℤ, ε ^ 2 = 1 ∧
      transportedMatrix w (fMatrix i) = ε • transportedMatrix z (fMatrix j) := by
  obtain ⟨ε, hε, h⟩ := transported_eMatrix_eq_sign_smul_of_rat_proportional (w ++ [i]) (z ++ [j]) i j q hq
  refine ⟨ε, hε, ?_⟩
  simpa only [transportedMatrix_append_simple_eMatrix, smul_neg, neg_inj] using h

/-- One integral sign simultaneously compares every positive divided power.
The factorials are cancelled over the integers before specialization. -/
theorem transported_eDividedPower_eq_sign_smul_of_rat_proportional
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

/-- One integral sign simultaneously compares every negative divided power,
using positive rational comparison along the appended routes. -/
theorem transported_fDividedPower_eq_sign_smul_of_rat_proportional
    (w z : List b.support) (i j : b.support) (q : ℚ)
    (hq : (titsConjugate (w ++ [i]) (eMatrix i)).map (algebraMap ℤ ℚ) =
      q • (titsConjugate (z ++ [j]) (eMatrix j)).map (algebraMap ℤ ℚ)) :
    ∃ ε : ℤ, ε ^ 2 = 1 ∧ ∀ n : ℕ,
      transportedMatrix w (fDividedPower i n) =
        ε ^ n • transportedMatrix z (fDividedPower j n) := by
  obtain ⟨ε, hε, h⟩ := transported_fMatrix_eq_sign_smul_of_rat_proportional w z i j q hq
  refine ⟨ε, hε, fun n => ?_⟩
  apply dividedPower_eq_sign_smul _ _ _ _ n ε _ _ h
  · rw [← transportedMatrix_pow, fMatrix_pow_eq_factorial_smul, transportedMatrix_smul]
  · rw [← transportedMatrix_pow, fMatrix_pow_eq_factorial_smul, transportedMatrix_smul]

/-- Rational proportionality of the actual positive transported operators implies
equality of every divided power over any commutative ring of characteristic two. -/
theorem specialize_transported_eDividedPower_eq_of_rat_proportional {S : Type*} [CommRing S] [CharP S 2]
    (w z : List b.support) (i j : b.support) (n : ℕ) (q : ℚ)
    (hq : (titsConjugate w (eMatrix i)).map (algebraMap ℤ ℚ) =
      q • (titsConjugate z (eMatrix j)).map (algebraMap ℤ ℚ)) :
    specializeMatrix (S := S) (transportedMatrix w (eDividedPower i n)) =
      specializeMatrix (S := S) (transportedMatrix z (eDividedPower j n)) := by
  obtain ⟨ε, hε, h⟩ := transported_eDividedPower_eq_sign_smul_of_rat_proportional w z i j q hq
  exact map_eq_of_sign_smul _ _ ε n hε (h n)

/-- Positive rational proportionality along the appended routes implies equality
of every negative divided power in characteristic two. -/
theorem specialize_transported_fDividedPower_eq_of_rat_proportional {S : Type*} [CommRing S] [CharP S 2]
    (w z : List b.support) (i j : b.support) (n : ℕ) (q : ℚ)
    (hq : (titsConjugate (w ++ [i]) (eMatrix i)).map (algebraMap ℤ ℚ) =
      q • (titsConjugate (z ++ [j]) (eMatrix j)).map (algebraMap ℤ ℚ)) :
    specializeMatrix (S := S) (transportedMatrix w (fDividedPower i n)) =
      specializeMatrix (S := S) (transportedMatrix z (fDividedPower j n)) := by
  obtain ⟨ε, hε, h⟩ := transported_fDividedPower_eq_sign_smul_of_rat_proportional w z i j q hq
  exact map_eq_of_sign_smul _ _ ε n hε (h n)


end Integral

section F4

open Theory.AlgebraicGroup.StandardRootSystem RootPairing.IntegralGeckConstruction
open scoped Classical

noncomputable local instance : Fintype typeF4Roots := Fintype.ofFinite _

/-- Integral positive route independence up to one sign in every degree. -/
theorem transported_eDividedPower_eq_sign_smul
    (w z : List typeF4RootPairing_base.support)
    (i j : typeF4RootPairing_base.support)
    (hroot : reflectionWord (P := typeF4RootPairing) w (i : typeF4Roots) =
      reflectionWord z (j : typeF4Roots)) :
    ∃ ε : ℤ, ε ^ 2 = 1 ∧ ∀ n : ℕ,
      transportedMatrix w (eDividedPower i n) =
        ε ^ n • transportedMatrix z (eDividedPower j n) := by
  obtain ⟨q, hq⟩ := exists_rat_smul_titsConjugate_of_reflectionWord_eq w z i j hroot
  exact transported_eDividedPower_eq_sign_smul_of_rat_proportional w z i j q hq

/-- Integral negative route independence up to one sign in every degree. -/
theorem transported_fDividedPower_eq_sign_smul
    (w z : List typeF4RootPairing_base.support)
    (i j : typeF4RootPairing_base.support)
    (hroot : reflectionWord (P := typeF4RootPairing) w (i : typeF4Roots) =
      reflectionWord z (j : typeF4Roots)) :
    ∃ ε : ℤ, ε ^ 2 = 1 ∧ ∀ n : ℕ,
      transportedMatrix w (fDividedPower i n) =
        ε ^ n • transportedMatrix z (fDividedPower j n) := by
  have hr : reflectionWord (P := typeF4RootPairing) (w ++ [i]) (i : typeF4Roots) =
      reflectionWord (z ++ [j]) (j : typeF4Roots) := by
    rw [reflectionWord_append_simple_self, reflectionWord_append_simple_self, hroot]
  obtain ⟨q, hq⟩ :=
    exists_rat_smul_titsConjugate_of_reflectionWord_eq (w ++ [i]) (z ++ [j]) i j hr
  exact transported_fDividedPower_eq_sign_smul_of_rat_proportional w z i j q hq

/-- Positive route independence for actual F4 divided powers in characteristic two. -/
theorem specialize_transported_eDividedPower_eq {S : Type*} [CommRing S] [CharP S 2]
    (w z : List typeF4RootPairing_base.support)
    (i j : typeF4RootPairing_base.support) (n : ℕ)
    (hroot : reflectionWord (P := typeF4RootPairing) w (i : typeF4Roots) =
      reflectionWord z (j : typeF4Roots)) :
    specializeMatrix (S := S) (transportedMatrix w (eDividedPower i n)) =
      specializeMatrix (S := S) (transportedMatrix z (eDividedPower j n)) := by
  obtain ⟨ε, hε, h⟩ := transported_eDividedPower_eq_sign_smul w z i j hroot
  exact map_eq_of_sign_smul _ _ ε n hε (h n)

/-- Negative route independence for actual F4 divided powers in characteristic two. -/
theorem specialize_transported_fDividedPower_eq {S : Type*} [CommRing S] [CharP S 2]
    (w z : List typeF4RootPairing_base.support)
    (i j : typeF4RootPairing_base.support) (n : ℕ)
    (hroot : reflectionWord (P := typeF4RootPairing) w (i : typeF4Roots) =
      reflectionWord z (j : typeF4Roots)) :
    specializeMatrix (S := S) (transportedMatrix w (fDividedPower i n)) =
      specializeMatrix (S := S) (transportedMatrix z (fDividedPower j n)) := by
  obtain ⟨ε, hε, h⟩ := transported_fDividedPower_eq_sign_smul w z i j hroot
  exact map_eq_of_sign_smul _ _ ε n hε (h n)

end F4

end ReeF4.WordRelations.RouteComparison
