module

public import Theory.AlgebraicGroup.RootSystems.GeckIrreducibleRationalRootspaceOne
public import Theory.AlgebraicGroup.RootSystems.IntegralRootCurveSimpleGeneration
public import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Relations
/-!
# Commuting canonical root curves from a common signed Weyl route

Distinct positive-negative simple Geck operators commute. A common integral
Tits conjugation preserves this identity. When its two endpoint roots are
positive, rational root-space multiplicity one compares both transported
operators with the actual canonical operators, even though their chosen routes
may differ. Injectivity of ℤ → ℚ then gives integral matrix commutation.

The factorial formulas imply commutation of every pair of divided powers by
cancellation over ℤ. Specializing afterwards proves commutation of the cubic
root curves over any commutative ring, including characteristic two. This is
the all-root form of the cancellation argument in `SimpleGeckGroup.Commutation`.

Source: Geck's integral construction and GLS3 §§2.4–2.6
(`refs/KGroup/GLS3/chapter2.tex`), as used for 2.3.6–7.
-/

namespace RootPairing.IntegralGeckConstruction
noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

private lemma nonsum_titsLift_conj_eMatrix (i : b.support) :
    titsLift i * eMatrix i * titsLiftInv i = -fMatrix i := by
  ext x y
  have h1 := congrFun₂ (titsLift_conj_eUnipotent i 1) x y
  have hm1 := congrFun₂ (titsLift_conj_eUnipotent i (-1)) x y
  have h2 := congrFun₂ (titsLift_conj_eUnipotent i 2) x y
  simp only [eUnipotent, fUnipotent, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.add_apply, Matrix.smul_apply, eDividedPower_one, fDividedPower_one,
    titsLift_mul_inv] at h1 hm1 h2
  norm_num at h1 hm1 h2
  change _ = - _
  omega

omit [P.IsReduced] in
private lemma nonsum_titsWordInv_append (w z : List b.support) :
    titsWordInv (w ++ z) = titsWordInv z * titsWordInv w := by
  induction w with
  | nil => simp [titsWordInv]
  | cons i w ih => simp [titsWordInv, ih, mul_assoc]

omit [P.IsReduced] in
private lemma nonsum_titsConjugate_append (w z : List b.support)
    (X : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    titsConjugate (w ++ z) X = titsConjugate w (titsConjugate z X) := by
  simp only [titsConjugate, titsWord_append, nonsum_titsWordInv_append, mul_assoc]

private lemma nonsum_titsConjugate_reflected_simple (w : List b.support) (i : b.support) :
    titsConjugate (w ++ [i]) (eMatrix i) = -titsConjugate w (fMatrix i) := by
  rw [nonsum_titsConjugate_append]
  have h : titsConjugate [i] (eMatrix i) = -fMatrix i := by
    simpa only [titsConjugate, titsWord, titsWordInv, mul_one, one_mul] using
      nonsum_titsLift_conj_eMatrix i
  rw [h]
  simp only [titsConjugate, Matrix.mul_neg, Matrix.neg_mul]

private lemma nonsum_commute_titsConjugate (w : List b.support)
    {X Y : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ} (h : Commute X Y) :
    Commute (titsConjugate w X) (titsConjugate w Y) := by
  change transportedMatrix w X * transportedMatrix w Y =
    transportedMatrix w Y * transportedMatrix w X
  rw [← transportedMatrix_mul, ← transportedMatrix_mul, h.eq]

private lemma nonsum_commute_eMatrix_fMatrix [P.IsIrreducible]
    (i j : b.support) (hij : i ≠ j) : Commute (eMatrix i) (fMatrix j) := by
  apply Matrix.map_injective (FaithfulSMul.algebraMap_injective ℤ R)
  simp only [Matrix.map_mul, map_eMatrix, map_fMatrix]
  simpa only [Ring.lie_def, sub_eq_zero] using GeckConstruction.lie_e_f_ne hij

/-- Common Weyl transport of two distinct, oppositely signed simple roots
proves commutation of the canonical positive integral operators. Rational
root-space comparison removes the dependence on the two chosen routes. -/
public theorem rootOperator_commute_of_common_signed_route [P.IsRootSystem] [P.IsIrreducible]
    (i j : ι) (hi : b.IsPos i) (hj : b.IsPos j)
    (w : List b.support) (l r : b.support) (hlr : l ≠ r)
    (hwi : reflectionWord w (l : ι) = i)
    (hwj : reflectionWord (w ++ [r]) (r : ι) = j) :
    Commute (rootOperator (P := P) (b := b) i) (rootOperator (P := P) (b := b) j) := by
  obtain ⟨a, ha⟩ := exists_rat_smul_titsConjugate_of_reflectionWord_eq
    (rootRoute (P := P) (b := b) i).word w
    (rootRoute (P := P) (b := b) i).simple l
    ((rootRoute (P := P) (b := b) i).target.trans hwi.symm)
  obtain ⟨c, hc⟩ := exists_rat_smul_titsConjugate_of_reflectionWord_eq
    (rootRoute (P := P) (b := b) j).word (w ++ [r])
    (rootRoute (P := P) (b := b) j).simple r
    ((rootRoute (P := P) (b := b) j).target.trans hwj.symm)
  have h := (nonsum_commute_titsConjugate w (nonsum_commute_eMatrix_fMatrix l r hlr)).neg_right
  rw [← nonsum_titsConjugate_reflected_simple] at h
  have hm := h.map (Int.castRingHom ℚ).mapMatrix
  have hs := (hm.smul_left a).smul_right c
  change Commute (a • (titsConjugate w (eMatrix l)).map (algebraMap ℤ ℚ))
    (c • (titsConjugate (w ++ [r]) (eMatrix r)).map (algebraMap ℤ ℚ)) at hs
  rw [← ha, ← hc] at hs
  apply Matrix.map_injective (FaithfulSMul.algebraMap_injective ℤ ℚ)
  simpa only [Matrix.map_mul, rootOperator_of_pos i hi, rootOperator_of_pos j hj,
    transportedMatrix, titsConjugate] using hs.eq

/-- Cancel factorials over the integral lattice before specializing to any
coefficient ring. -/
public theorem rootDividedPower_commute_of_operator_commute {i j : ι}
    (h : Commute (rootOperator (P := P) (b := b) i) (rootOperator (P := P) (b := b) j))
    (a c : ℕ) : Commute (rootDividedPower (P := P) (b := b) i a)
      (rootDividedPower (P := P) (b := b) j c) := by
  have hh := (h.pow_pow a c).eq
  rw [rootOperator_pow_eq_factorial_smul, rootOperator_pow_eq_factorial_smul] at hh
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul] at hh
  rw [Nat.mul_comm c.factorial a.factorial] at hh
  ext x y
  exact nsmul_right_injective (Nat.mul_ne_zero (Nat.factorial_ne_zero a)
    (Nat.factorial_ne_zero c)) (congrFun₂ hh x y)

/-- Commuting canonical integral root operators give commuting canonical
root curves over every commutative coefficient ring. -/
public theorem rootCurveUnit_commute_of_operator_commute {S : Type*} [CommRing S] {i j : ι}
    (h : Commute (rootOperator (P := P) (b := b) i) (rootOperator (P := P) (b := b) j))
    (t u : S) : Commute
      (rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) i t)
      (rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) j u) := by
  have hc (a c : ℕ) :
      Commute (specializeMatrix (S := S) (rootDividedPower (P := P) (b := b) i a))
        (specializeMatrix (S := S) (rootDividedPower (P := P) (b := b) j c)) :=
    (rootDividedPower_commute_of_operator_commute h a c).map (Int.castRingHom S).mapMatrix
  have hs (a c : ℕ) (x y : S) :
      Commute (x • specializeMatrix (rootDividedPower (P := P) (b := b) i a))
        (y • specializeMatrix (rootDividedPower (P := P) (b := b) j c)) :=
    ((hc a c).smul_left x).smul_right y
  apply Units.ext
  change Commute (rootCurveMatrix _ i t) (rootCurveMatrix _ j u)
  unfold rootCurveMatrix
  change Commute
    (1 + t • specializeMatrix (rootDividedPower (P := P) (b := b) i 1) +
      t ^ 2 • specializeMatrix (rootDividedPower (P := P) (b := b) i 2) +
      t ^ 3 • specializeMatrix (rootDividedPower (P := P) (b := b) i 3))
    (1 + u • specializeMatrix (rootDividedPower (P := P) (b := b) j 1) +
      u ^ 2 • specializeMatrix (rootDividedPower (P := P) (b := b) j 2) +
      u ^ 3 • specializeMatrix (rootDividedPower (P := P) (b := b) j 3))
  apply Commute.add_left
  · apply Commute.add_left
    · apply Commute.add_left
      · exact Commute.one_left _
      · exact (((Commute.one_right _).add_right (hs 1 1 t u)).add_right
          (hs 1 2 t (u ^ 2))).add_right (hs 1 3 t (u ^ 3))
    · exact (((Commute.one_right _).add_right (hs 2 1 (t ^ 2) u)).add_right
        (hs 2 2 (t ^ 2) (u ^ 2))).add_right (hs 2 3 (t ^ 2) (u ^ 3))
  · exact (((Commute.one_right _).add_right (hs 3 1 (t ^ 3) u)).add_right
      (hs 3 2 (t ^ 3) (u ^ 2))).add_right (hs 3 3 (t ^ 3) (u ^ 3))
end
end RootPairing.IntegralGeckConstruction
