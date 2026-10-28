module

public import Theory.AlgebraicGroup.Borel.IntegralChevalleyRootOperators
public import Theory.AlgebraicGroup.Morphism.ClosedEmbedding
public import Theory.AlgebraicGroup.Representations.Matrix
public import Theory.AlgebraicGroup.Unipotent.OneParameter
public import Theory.AlgebraicGroup.Variety.AffineDuality
public import Mathlib.LinearAlgebra.Matrix.Integer
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo

/-!
# Characteristic-free integral Chevalley root curves

This module specializes the integral all-root divided powers of
`IntegralChevalleyRootOperators` to an arbitrary algebraically closed field.  For every
root it constructs the cubic polynomial exponential in the specialized Chevalley lattice,
proves its additive and inverse laws without division, and realizes it as a regular morphism
from `KPlus` into the ambient general linear variety.  Its image is an injectively
parametrized closed one-parameter subgroup.  The morphisms and their point values form one
globally normalized root-indexed family, with point-valued `n` and `h` elements in the exact
factor order expected by `IsChevalleySystem`.

The algebraic proof expands the divided-power convolution identities through degree three;
all higher products vanish integrally.  Injectivity is characteristic-free: conjugating by
the integral Tits word reduces every root curve to a simple-root curve with a coefficient
equal to its parameter.  That same coefficient is a polynomial function on `GL`, supplying
the coordinate-preimage hypothesis for the closed-image isomorphism.  Finally, a direct
two-by-two calculation records the convention
`n_alpha(t) = [[0,t],[-t⁻¹,0]]` and `h_alpha(t) = diag(t⁻¹,t)`.

The construction follows GLS3, Theorem 1.12.1 and Remark 1.12.10, and Steinberg,
*Lectures on Chevalley Groups*, using only the integral operator package proved in the
preceding module.  In particular it does not depend on any numbered Chevalley-existence
declaration.
-/

open scoped Matrix

namespace RootPairing.IntegralGeckConstruction

@[expose] public section

noncomputable section

variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

/-- Scalar extension of an integral Chevalley matrix. -/
def specializeMatrix {S : Type*} [Ring S]
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) S :=
  A.map (Int.castRingHom S)

omit [CharZero R] [P.IsCrystallographic] [P.IsReduced] [DecidableEq ι] in
lemma specializeMatrix_mul {S : Type*} [Ring S]
    (A B : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    specializeMatrix (S := S) (A * B) =
      specializeMatrix (S := S) A * specializeMatrix (S := S) B :=
  Matrix.map_mul_intCast A B

omit [CharZero R] [P.IsCrystallographic] [P.IsReduced] [Fintype ι]
  [DecidableEq ι] in
lemma specializeMatrix_nsmul {S : Type*} [Ring S] (n : ℕ)
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    specializeMatrix (S := S) (n • A) =
      (n : S) • specializeMatrix (S := S) A := by
  ext i j
  change ((((n : ℕ) : ℤ) * A i j : ℤ) : S) = (n : S) * (A i j : S)
  rw [Int.cast_mul, Int.cast_natCast]

omit [CharZero R] [P.IsCrystallographic] [P.IsReduced] [Fintype ι]
  [DecidableEq ι] in
@[simp] lemma specializeMatrix_zero {S : Type*} [Ring S] :
    specializeMatrix (S := S) (0 : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) = 0 := by
  ext i j
  simp [specializeMatrix]

omit [CharZero R] [P.IsCrystallographic] [P.IsReduced] [Fintype ι] in
@[simp] lemma specializeMatrix_one {S : Type*} [Ring S] :
    specializeMatrix (S := S) (1 : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) = 1 := by
  ext i j
  simp [specializeMatrix, Matrix.one_apply]

omit [P.IsReduced] in
lemma specializeMatrix_transportedMatrix {S : Type*} [Ring S]
    (word : List b.support)
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ) :
    specializeMatrix (S := S) (transportedMatrix (P := P) word A) =
      specializeMatrix (S := S) (titsWord (P := P) word) *
        specializeMatrix (S := S) A *
          specializeMatrix (S := S) (titsWordInv (P := P) word) := by
  simp only [transportedMatrix, specializeMatrix_mul]

/-- The degree-three exponential attached to an integral root-operator certificate. -/
def rootCurveMatrix {S : Type*} [CommRing S]
    (D : IntegralChevalleyRootOperators P b) (i : ι) (t : S) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) S :=
  1 + t • specializeMatrix (S := S) (D.rootDividedPower i 1) +
    t ^ 2 • specializeMatrix (S := S) (D.rootDividedPower i 2) +
    t ^ 3 • specializeMatrix (S := S) (D.rootDividedPower i 3)

private def simplePositiveCurveMatrix {S : Type*} [CommRing S]
    (i : b.support) (t : S) : Matrix (b.support ⊕ ι) (b.support ⊕ ι) S :=
  1 + t • specializeMatrix (S := S) (eDividedPower (P := P) i 1) +
    t ^ 2 • specializeMatrix (S := S) (eDividedPower (P := P) i 2) +
    t ^ 3 • specializeMatrix (S := S) (eDividedPower (P := P) i 3)

private def simpleNegativeCurveMatrix {S : Type*} [CommRing S]
    (i : b.support) (t : S) : Matrix (b.support ⊕ ι) (b.support ⊕ ι) S :=
  1 + t • specializeMatrix (S := S) (fDividedPower (P := P) i 1) +
    t ^ 2 • specializeMatrix (S := S) (fDividedPower (P := P) i 2) +
    t ^ 3 • specializeMatrix (S := S) (fDividedPower (P := P) i 3)

private lemma canonicalRootCurveMatrix_of_pos {S : Type*} [CommRing S]
    (i : ι) (hi : b.IsPos i) (t : S) :
    rootCurveMatrix (integralChevalleyRootOperators (P := P) (b := b)) i t =
      specializeMatrix (S := S)
          (titsWord (P := P) (rootRoute (P := P) (b := b) i).word) *
        simplePositiveCurveMatrix (P := P)
          (rootRoute (P := P) (b := b) i).simple t *
        specializeMatrix (S := S)
          (titsWordInv (P := P) (rootRoute (P := P) (b := b) i).word) := by
  let _ := P.indexNeg
  change 1 + t • specializeMatrix (S := S) (rootDividedPower (P := P) (b := b) i 1) +
      t ^ 2 • specializeMatrix (S := S) (rootDividedPower (P := P) (b := b) i 2) +
      t ^ 3 • specializeMatrix (S := S) (rootDividedPower (P := P) (b := b) i 3) = _
  rw [rootDividedPower_of_pos i hi, rootDividedPower_of_pos i hi,
    rootDividedPower_of_pos i hi]
  simp only [specializeMatrix_transportedMatrix]
  have hTU :
      specializeMatrix (S := S)
          (titsWord (P := P) (rootRoute (P := P) (b := b) i).word) *
        specializeMatrix (S := S)
          (titsWordInv (P := P) (rootRoute (P := P) (b := b) i).word) = 1 := by
    rw [← specializeMatrix_mul, titsWord_mul_inv, specializeMatrix_one]
  simp only [simplePositiveCurveMatrix, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  noncomm_ring [hTU]

private lemma canonicalRootCurveMatrix_of_neg {S : Type*} [CommRing S]
    (i : ι) (hi : ¬ b.IsPos i) (t : S) :
    letI := P.indexNeg
    rootCurveMatrix (integralChevalleyRootOperators (P := P) (b := b)) i t =
      specializeMatrix (S := S)
          (titsWord (P := P) (rootRoute (P := P) (b := b) (-i)).word) *
        simpleNegativeCurveMatrix (P := P)
          (rootRoute (P := P) (b := b) (-i)).simple t *
        specializeMatrix (S := S)
          (titsWordInv (P := P) (rootRoute (P := P) (b := b) (-i)).word) := by
  let _ := P.indexNeg
  change 1 + t • specializeMatrix (S := S) (rootDividedPower (P := P) (b := b) i 1) +
      t ^ 2 • specializeMatrix (S := S) (rootDividedPower (P := P) (b := b) i 2) +
      t ^ 3 • specializeMatrix (S := S) (rootDividedPower (P := P) (b := b) i 3) = _
  simp only [rootDividedPower, dif_neg hi]
  simp only [specializeMatrix_transportedMatrix]
  have hTU :
      specializeMatrix (S := S)
          (titsWord (P := P) (rootRoute (P := P) (b := b) (-i)).word) *
        specializeMatrix (S := S)
          (titsWordInv (P := P) (rootRoute (P := P) (b := b) (-i)).word) = 1 := by
    rw [← specializeMatrix_mul, titsWord_mul_inv, specializeMatrix_one]
  simp only [simpleNegativeCurveMatrix, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  noncomm_ring [hTU]

omit [P.IsReduced] in
private lemma simplePositiveCurveMatrix_recovery {S : Type*} [CommRing S]
    (i : b.support) (t : S) :
    letI := P.indexNeg
    simplePositiveCurveMatrix (P := P) i t (Sum.inl i) (Sum.inr (-i : ι)) = t := by
  let _ := P.indexNeg
  simp [simplePositiveCurveMatrix, specializeMatrix, eDividedPower, eMatrix]

private lemma simpleNegativeCurveMatrix_eq_omega {S : Type*} [CommRing S]
    (i : b.support) (t : S) :
    simpleNegativeCurveMatrix (P := P) i t =
      specializeMatrix (S := S) (omegaMatrix (P := P) (b := b)) *
        simplePositiveCurveMatrix (P := P) i t *
        specializeMatrix (S := S) (omegaMatrix (P := P) (b := b)) := by
  have hsq :
      specializeMatrix (S := S) (omegaMatrix (P := P) (b := b)) *
          specializeMatrix (S := S) (omegaMatrix (P := P) (b := b)) = 1 := by
    rw [← specializeMatrix_mul, omegaMatrix_sq, specializeMatrix_one]
  simp only [simpleNegativeCurveMatrix, simplePositiveCurveMatrix, fDividedPower,
    specializeMatrix_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul]
  noncomm_ring [hsq]

private lemma simpleNegativeCurveMatrix_recovery {S : Type*} [CommRing S]
    (i : b.support) (t : S) :
    simpleNegativeCurveMatrix (P := P) i t (Sum.inl i) (Sum.inr (i : ι)) = t := by
  let _ := P.indexNeg
  rw [simpleNegativeCurveMatrix_eq_omega]
  simp [Matrix.mul_apply, specializeMatrix, omegaMatrix,
    Matrix.one_apply]
  simpa only [P.indexNeg_neg] using
    simplePositiveCurveMatrix_recovery (P := P) i t

private def rootRecoveryWord (i : ι) : List b.support := by
  classical
  let _ := P.indexNeg
  exact if hi : b.IsPos i then
    (rootRoute (P := P) (b := b) i).word
  else
    (rootRoute (P := P) (b := b) (-i)).word

private def rootRecoverySimple (i : ι) : b.support := by
  classical
  let _ := P.indexNeg
  exact if hi : b.IsPos i then
    (rootRoute (P := P) (b := b) i).simple
  else
    (rootRoute (P := P) (b := b) (-i)).simple

private def rootRecoveryColumn (i : ι) : b.support ⊕ ι := by
  classical
  letI := P.indexNeg
  exact if hi : b.IsPos i then
    Sum.inr (-(rootRoute (P := P) (b := b) i).simple : ι)
  else
    Sum.inr ((rootRoute (P := P) (b := b) (-i)).simple : ι)

/-- The Tits-conjugated matrix coefficient that recovers the root parameter. -/
private def rootRecoveryValue {S : Type*} [CommRing S] (i : ι)
    (A : Matrix (b.support ⊕ ι) (b.support ⊕ ι) S) : S :=
  (specializeMatrix (S := S)
      (titsWordInv (P := P) (rootRecoveryWord (P := P) (b := b) i)) * A *
    specializeMatrix (S := S)
      (titsWord (P := P) (rootRecoveryWord (P := P) (b := b) i)))
    (Sum.inl (rootRecoverySimple (P := P) (b := b) i))
    (rootRecoveryColumn (P := P) (b := b) i)

/-- The canonical integral root curve has a characteristic-free linear recovery coordinate. -/
private theorem rootRecoveryValue_rootCurveMatrix {S : Type*} [CommRing S]
    (i : ι) (t : S) :
    rootRecoveryValue (P := P) (b := b) i
        (rootCurveMatrix (integralChevalleyRootOperators (P := P) (b := b)) i t) = t := by
  classical
  let _ := P.indexNeg
  by_cases hi : b.IsPos i
  · simp only [rootRecoveryValue, rootRecoveryWord, rootRecoverySimple,
      rootRecoveryColumn, dif_pos hi]
    rw [canonicalRootCurveMatrix_of_pos i hi t]
    have hUT :
        specializeMatrix (S := S)
            (titsWordInv (P := P) (rootRoute (P := P) (b := b) i).word) *
          specializeMatrix (S := S)
            (titsWord (P := P) (rootRoute (P := P) (b := b) i).word) = 1 := by
      rw [← specializeMatrix_mul, titsWord_inv_mul, specializeMatrix_one]
    rw [show
      specializeMatrix (S := S)
            (titsWordInv (P := P) (rootRoute (P := P) (b := b) i).word) *
          (specializeMatrix (S := S)
              (titsWord (P := P) (rootRoute (P := P) (b := b) i).word) *
            simplePositiveCurveMatrix (P := P)
              (rootRoute (P := P) (b := b) i).simple t *
            specializeMatrix (S := S)
              (titsWordInv (P := P) (rootRoute (P := P) (b := b) i).word)) *
          specializeMatrix (S := S)
            (titsWord (P := P) (rootRoute (P := P) (b := b) i).word) =
        simplePositiveCurveMatrix (P := P)
          (rootRoute (P := P) (b := b) i).simple t by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc, hUT, Matrix.one_mul, Matrix.mul_one]]
    exact simplePositiveCurveMatrix_recovery
      (P := P) (rootRoute (P := P) (b := b) i).simple t
  · simp only [rootRecoveryValue, rootRecoveryWord, rootRecoverySimple,
      rootRecoveryColumn, dif_neg hi]
    rw [canonicalRootCurveMatrix_of_neg i hi t]
    have hUT :
        specializeMatrix (S := S)
            (titsWordInv (P := P) (rootRoute (P := P) (b := b) (-i)).word) *
          specializeMatrix (S := S)
            (titsWord (P := P) (rootRoute (P := P) (b := b) (-i)).word) = 1 := by
      rw [← specializeMatrix_mul, titsWord_inv_mul, specializeMatrix_one]
    rw [show
      specializeMatrix (S := S)
            (titsWordInv (P := P) (rootRoute (P := P) (b := b) (-i)).word) *
          (specializeMatrix (S := S)
              (titsWord (P := P) (rootRoute (P := P) (b := b) (-i)).word) *
            simpleNegativeCurveMatrix (P := P)
              (rootRoute (P := P) (b := b) (-i)).simple t *
            specializeMatrix (S := S)
              (titsWordInv (P := P) (rootRoute (P := P) (b := b) (-i)).word)) *
          specializeMatrix (S := S)
            (titsWord (P := P) (rootRoute (P := P) (b := b) (-i)).word) =
        simpleNegativeCurveMatrix (P := P)
          (rootRoute (P := P) (b := b) (-i)).simple t by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc, hUT, Matrix.one_mul, Matrix.mul_one]]
    exact simpleNegativeCurveMatrix_recovery
      (P := P) (rootRoute (P := P) (b := b) (-i)).simple t

private lemma cubicCurve_add {S A : Type*} [CommRing S] [Ring A] [Algebra S A]
    (X1 X2 X3 : A)
    (h11 : X1 * X1 = (2 : S) • X2)
    (h12 : X1 * X2 = (3 : S) • X3)
    (h21 : X2 * X1 = (3 : S) • X3)
    (h13 : X1 * X3 = 0) (h31 : X3 * X1 = 0)
    (h22 : X2 * X2 = 0) (h23 : X2 * X3 = 0)
    (h32 : X3 * X2 = 0) (h33 : X3 * X3 = 0)
    (a c : S) :
    1 + (a + c) • X1 + (a + c) ^ 2 • X2 + (a + c) ^ 3 • X3 =
      (1 + a • X1 + a ^ 2 • X2 + a ^ 3 • X3) *
        (1 + c • X1 + c ^ 2 • X2 + c ^ 3 • X3) := by
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, smul_smul, h11, h12, h21, h13, h31, h22, h23, h32, h33]
  module

private lemma specializedCubicRelations {S : Type*} [CommRing S]
    (D : IntegralChevalleyRootOperators P b) (i : ι) :
    let X1 := specializeMatrix (S := S) (D.rootDividedPower i 1)
    let X2 := specializeMatrix (S := S) (D.rootDividedPower i 2)
    let X3 := specializeMatrix (S := S) (D.rootDividedPower i 3)
    X1 * X1 = (2 : S) • X2 ∧ X1 * X2 = (3 : S) • X3 ∧
      X2 * X1 = (3 : S) • X3 ∧ X1 * X3 = 0 ∧ X3 * X1 = 0 ∧
      X2 * X2 = 0 ∧ X2 * X3 = 0 ∧ X3 * X2 = 0 ∧ X3 * X3 = 0 := by
  dsimp
  have hzero (m n : ℕ) (hmn : 4 ≤ m + n) :
      specializeMatrix (S := S)
          (D.rootDividedPower i m * D.rootDividedPower i n) = 0 := by
    rw [D.dividedPower_mul, D.dividedPower_eq_zero_of_four_le i (m + n) hmn,
      smul_zero, specializeMatrix_zero]
  constructor
  · rw [← specializeMatrix_mul, D.dividedPower_mul, specializeMatrix_nsmul]
    norm_num
  constructor
  · rw [← specializeMatrix_mul, D.dividedPower_mul, specializeMatrix_nsmul]
    norm_num
  constructor
  · rw [← specializeMatrix_mul, D.dividedPower_mul, specializeMatrix_nsmul]
    norm_num
  constructor
  · rw [← specializeMatrix_mul]
    exact hzero 1 3 (by omega)
  constructor
  · rw [← specializeMatrix_mul]
    exact hzero 3 1 (by omega)
  constructor
  · rw [← specializeMatrix_mul]
    exact hzero 2 2 (by omega)
  constructor
  · rw [← specializeMatrix_mul]
    exact hzero 2 3 (by omega)
  constructor
  · rw [← specializeMatrix_mul]
    exact hzero 3 2 (by omega)
  · rw [← specializeMatrix_mul]
    exact hzero 3 3 (by omega)

/-- The characteristic-free additive law for every specialized root curve. -/
theorem rootCurveMatrix_add {S : Type*} [CommRing S]
    (D : IntegralChevalleyRootOperators P b) (i : ι) (s t : S) :
    rootCurveMatrix D i (s + t) = rootCurveMatrix D i s * rootCurveMatrix D i t := by
  rcases specializedCubicRelations (S := S) D i with
    ⟨h11, h12, h21, h13, h31, h22, h23, h32, h33⟩
  exact cubicCurve_add _ _ _ h11 h12 h21 h13 h31 h22 h23 h32 h33 s t

@[simp] theorem rootCurveMatrix_zero {S : Type*} [CommRing S]
    (D : IntegralChevalleyRootOperators P b) (i : ι) :
    rootCurveMatrix (S := S) D i 0 = 1 := by
  simp [rootCurveMatrix]

/-- The root curve as a unit; its inverse is evaluation at the negated parameter. -/
def rootCurveUnit {S : Type*} [CommRing S]
    (D : IntegralChevalleyRootOperators P b) (i : ι) (t : S) :
    (Matrix (b.support ⊕ ι) (b.support ⊕ ι) S)ˣ where
  val := rootCurveMatrix D i t
  inv := rootCurveMatrix D i (-t)
  val_inv := by rw [← rootCurveMatrix_add]; simp
  inv_val := by rw [← rootCurveMatrix_add]; simp

@[simp] theorem rootCurveUnit_zero {S : Type*} [CommRing S]
    (D : IntegralChevalleyRootOperators P b) (i : ι) :
    rootCurveUnit (S := S) D i 0 = 1 := by
  apply Units.ext
  exact rootCurveMatrix_zero D i

theorem rootCurveUnit_add {S : Type*} [CommRing S]
    (D : IntegralChevalleyRootOperators P b) (i : ι) (s t : S) :
    rootCurveUnit D i (s + t) = rootCurveUnit D i s * rootCurveUnit D i t := by
  apply Units.ext
  exact rootCurveMatrix_add D i s t

theorem rootCurveUnit_inv {S : Type*} [CommRing S]
    (D : IntegralChevalleyRootOperators P b) (i : ι) (t : S) :
    (rootCurveUnit D i t)⁻¹ = rootCurveUnit D i (-t) := by
  apply Units.ext
  rfl

open Theory AlgebraicGroup

variable {k : Type*} [Field k] [IsAlgClosed k]

/-- The specialized Chevalley lattice over `k`. -/
abbrev SpecializedCarrier := b.support ⊕ ι → k

/-- The ambient general-linear variety of the specialized Chevalley lattice. -/
noncomputable abbrev RootCurveAmbient :=
  Theory.AlgebraicGroup.glVariety
    (Module.finrank k (SpecializedCarrier (b := b) (ι := ι) (k := k))) (k := k)

/-- The canonical integral root curve specialized to `k`. -/
def canonicalRootCurveMatrix (i : ι) (t : k) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) k :=
  rootCurveMatrix (integralChevalleyRootOperators (P := P) (b := b)) i t

/-- The canonical specialized root curve as a matrix unit. -/
def canonicalRootCurveUnit (i : ι) (t : k) :
    (Matrix (b.support ⊕ ι) (b.support ⊕ ι) k)ˣ :=
  rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) i t

omit [IsAlgClosed k] in
@[simp] theorem canonicalRootCurveUnit_zero (i : ι) :
    canonicalRootCurveUnit (P := P) (b := b) (k := k) i 0 = 1 :=
  rootCurveUnit_zero _ _

omit [IsAlgClosed k] in
theorem canonicalRootCurveUnit_add (i : ι) (s t : k) :
    canonicalRootCurveUnit (P := P) (b := b) i (s + t) =
      canonicalRootCurveUnit (P := P) (b := b) i s *
        canonicalRootCurveUnit (P := P) (b := b) i t :=
  rootCurveUnit_add _ _ _ _

omit [IsAlgClosed k] in
theorem canonicalRootCurveUnit_inv (i : ι) (t : k) :
    (canonicalRootCurveUnit (P := P) (b := b) i t)⁻¹ =
      canonicalRootCurveUnit (P := P) (b := b) i (-t) :=
  rootCurveUnit_inv _ _ _

noncomputable def rootCoordinatePolynomial (i : ι)
    (row column : b.support ⊕ ι) : MvPolynomial PUnit k :=
  let D := integralChevalleyRootOperators (P := P) (b := b)
  MvPolynomial.C ((1 : Matrix (b.support ⊕ ι) (b.support ⊕ ι) k) row column) +
    MvPolynomial.X PUnit.unit *
      MvPolynomial.C (specializeMatrix (S := k) (D.rootDividedPower i 1) row column) +
    MvPolynomial.X PUnit.unit ^ 2 *
      MvPolynomial.C (specializeMatrix (S := k) (D.rootDividedPower i 2) row column) +
    MvPolynomial.X PUnit.unit ^ 3 *
      MvPolynomial.C (specializeMatrix (S := k) (D.rootDividedPower i 3) row column)

noncomputable def rootInverseCoordinatePolynomial (i : ι)
    (row column : b.support ⊕ ι) : MvPolynomial PUnit k :=
  let D := integralChevalleyRootOperators (P := P) (b := b)
  MvPolynomial.C ((1 : Matrix (b.support ⊕ ι) (b.support ⊕ ι) k) row column) -
    MvPolynomial.X PUnit.unit *
      MvPolynomial.C (specializeMatrix (S := k) (D.rootDividedPower i 1) row column) +
    MvPolynomial.X PUnit.unit ^ 2 *
      MvPolynomial.C (specializeMatrix (S := k) (D.rootDividedPower i 2) row column) -
    MvPolynomial.X PUnit.unit ^ 3 *
      MvPolynomial.C (specializeMatrix (S := k) (D.rootDividedPower i 3) row column)

omit [IsAlgClosed k] in
lemma eval_rootCoordinatePolynomial (i : ι) (row column : b.support ⊕ ι)
    (x : Variety.Point (KPlus k)) :
    evalPolynomial x.val (rootCoordinatePolynomial (P := P) (b := b) i row column) =
      canonicalRootCurveMatrix (P := P) (b := b) i (x.val PUnit.unit) row column := by
  simp [rootCoordinatePolynomial, canonicalRootCurveMatrix, rootCurveMatrix, evalPolynomial]

omit [IsAlgClosed k] in
lemma eval_rootInverseCoordinatePolynomial (i : ι)
    (row column : b.support ⊕ ι) (x : Variety.Point (KPlus k)) :
    evalPolynomial x.val
        (rootInverseCoordinatePolynomial (P := P) (b := b) i row column) =
      canonicalRootCurveMatrix (P := P) (b := b) i (-x.val PUnit.unit) row column := by
  simp [rootInverseCoordinatePolynomial, canonicalRootCurveMatrix,
    rootCurveMatrix, evalPolynomial]
  ring

noncomputable def carrierIndexEquiv :
    (b.support ⊕ ι) ≃
      Fin (Module.finrank k (SpecializedCarrier (b := b) (ι := ι) (k := k))) :=
  let h : Module.finrank k (SpecializedCarrier (b := b) (ι := ι) (k := k)) =
      Fintype.card (b.support ⊕ ι) := Module.finrank_pi k
  (Fintype.equivFin (b.support ⊕ ι)).trans (Equiv.cast (congrArg Fin h.symm))

noncomputable def carrierBasis :
    Module.Basis
      (Fin (Module.finrank k (SpecializedCarrier (b := b) (ι := ι) (k := k))))
      k (SpecializedCarrier (b := b) (ι := ι) (k := k)) :=
  (Pi.basisFun k (b.support ⊕ ι)).reindex
    (carrierIndexEquiv (b := b) (ι := ι) (k := k))

noncomputable def rootPointRepresentation (i : ι) :
    Variety.Point (KPlus k) →*
      LinearMap.GeneralLinearGroup k (SpecializedCarrier (b := b) (ι := ι) (k := k)) where
  toFun := fun x => Matrix.GeneralLinearGroup.toLin
    (canonicalRootCurveUnit (P := P) (b := b) i (x.val PUnit.unit))
  map_one' := by
    have hcoord : ((1 : Variety.Point (KPlus k)).val PUnit.unit) = 0 := by
      rw [← kPlusPoint_coordinate (k := k) (1 : Variety.Point (KPlus k))]
      rfl
    change Matrix.GeneralLinearGroup.toLin
      (canonicalRootCurveUnit (P := P) (b := b) i
        ((1 : Variety.Point (KPlus k)).val PUnit.unit)) = 1
    rw [hcoord, canonicalRootCurveUnit_zero]
    exact map_one _
  map_mul' := by
    intro x y
    change Matrix.GeneralLinearGroup.toLin
      (canonicalRootCurveUnit (P := P) (b := b) i ((x * y).val PUnit.unit)) =
      Matrix.GeneralLinearGroup.toLin
          (canonicalRootCurveUnit (P := P) (b := b) i (x.val PUnit.unit)) *
        Matrix.GeneralLinearGroup.toLin
          (canonicalRootCurveUnit (P := P) (b := b) i (y.val PUnit.unit))
    rw [kPlusPoint_coordinate_mul, canonicalRootCurveUnit_add, map_mul]

noncomputable def rootMatrixCoefficient (i : ι)
    (row column : Fin (Module.finrank k
      (SpecializedCarrier (b := b) (ι := ι) (k := k)))) :
    (KPlus k).PolynomialFunction :=
  Variety.PolynomialFunction.ofPolynomial (KPlus k)
    (rootCoordinatePolynomial (P := P) (b := b) i
      ((carrierIndexEquiv (b := b) (ι := ι) (k := k)).symm row)
      ((carrierIndexEquiv (b := b) (ι := ι) (k := k)).symm column))

noncomputable def rootInverseMatrixCoefficient (i : ι)
    (row column : Fin (Module.finrank k
      (SpecializedCarrier (b := b) (ι := ι) (k := k)))) :
    (KPlus k).PolynomialFunction :=
  Variety.PolynomialFunction.ofPolynomial (KPlus k)
    (rootInverseCoordinatePolynomial (P := P) (b := b) i
      ((carrierIndexEquiv (b := b) (ι := ι) (k := k)).symm row)
      ((carrierIndexEquiv (b := b) (ι := ι) (k := k)).symm column))

omit [IsAlgClosed k] in
lemma rootMatrixCoefficient_apply (i : ι)
    (row column : Fin (Module.finrank k
      (SpecializedCarrier (b := b) (ι := ι) (k := k))))
    (x : Variety.Point (KPlus k)) :
    rootMatrixCoefficient (P := P) (b := b) i row column x =
      (carrierBasis (b := b) (ι := ι) (k := k)).repr
        (((rootPointRepresentation (P := P) (b := b) i x :
            LinearMap.GeneralLinearGroup k
              (SpecializedCarrier (b := b) (ι := ι) (k := k))) :
          Module.End k (SpecializedCarrier (b := b) (ι := ι) (k := k)))
          ((carrierBasis (b := b) (ι := ι) (k := k)) column)) row := by
  change evalPolynomial x.val
    (rootCoordinatePolynomial (P := P) (b := b) i
      ((carrierIndexEquiv (b := b) (ι := ι) (k := k)).symm row)
      ((carrierIndexEquiv (b := b) (ι := ι) (k := k)).symm column)) = _
  rw [eval_rootCoordinatePolynomial]
  simp [carrierBasis, rootPointRepresentation, Module.Basis.reindex_apply]
  rfl

omit [IsAlgClosed k] in
lemma rootInverseMatrixCoefficient_apply (i : ι)
    (row column : Fin (Module.finrank k
      (SpecializedCarrier (b := b) (ι := ι) (k := k))))
    (x : Variety.Point (KPlus k)) :
    rootInverseMatrixCoefficient (P := P) (b := b) i row column x =
      (carrierBasis (b := b) (ι := ι) (k := k)).repr
        (((((rootPointRepresentation (P := P) (b := b) i x)⁻¹ :
            LinearMap.GeneralLinearGroup k
              (SpecializedCarrier (b := b) (ι := ι) (k := k))) :
          Module.End k (SpecializedCarrier (b := b) (ι := ι) (k := k)))
          ((carrierBasis (b := b) (ι := ι) (k := k)) column))) row := by
  change evalPolynomial x.val
    (rootInverseCoordinatePolynomial (P := P) (b := b) i
      ((carrierIndexEquiv (b := b) (ι := ι) (k := k)).symm row)
      ((carrierIndexEquiv (b := b) (ι := ι) (k := k)).symm column)) = _
  rw [eval_rootInverseCoordinatePolynomial]
  have hinv : (rootPointRepresentation (P := P) (b := b) i x)⁻¹ =
      Matrix.GeneralLinearGroup.toLin
        (canonicalRootCurveUnit (P := P) (b := b) i (-x.val PUnit.unit)) := by
    change (Matrix.GeneralLinearGroup.toLin
      (canonicalRootCurveUnit (P := P) (b := b) i (x.val PUnit.unit)))⁻¹ = _
    rw [← map_inv, canonicalRootCurveUnit_inv]
  rw [hinv]
  simp [carrierBasis, Module.Basis.reindex_apply]
  rfl

/-- The globally normalized family of regular root morphisms into the specialized `GL`. -/
noncomputable def rootMorphism (i : ι) :
    AlgebraicGroup.Morphism (KPlus k)
      (RootCurveAmbient (b := b) (ι := ι) (k := k)) := by
  simpa [RootCurveAmbient] using
    generalLinearRepresentationMorphismOfInverseMatrixCoefficient
      (carrierBasis (b := b) (ι := ι) (k := k))
      (rootPointRepresentation (P := P) (b := b) i)
      (rootMatrixCoefficient (P := P) (b := b) i)
      (rootInverseMatrixCoefficient (P := P) (b := b) i)
      (rootMatrixCoefficient_apply (P := P) (b := b) i)
      (rootInverseMatrixCoefficient_apply (P := P) (b := b) i)

omit [IsAlgClosed k] in
@[simp] theorem rootMorphism_apply (i : ι) (x : Variety.Point (KPlus k)) :
    (rootMorphism (P := P) (b := b) i).onPoints x =
      generalLinearRepresentationPoint (carrierBasis (b := b) (ι := ι) (k := k))
        (rootPointRepresentation (P := P) (b := b) i x) := by
  rw [rootMorphism]
  exact generalLinearRepresentationMorphismOfInverseMatrixCoefficient_apply
    (carrierBasis (b := b) (ι := ι) (k := k))
    (rootPointRepresentation (P := P) (b := b) i)
    (rootMatrixCoefficient (P := P) (b := b) i)
    (rootInverseMatrixCoefficient (P := P) (b := b) i)
    (rootMatrixCoefficient_apply (P := P) (b := b) i)
    (rootInverseMatrixCoefficient_apply (P := P) (b := b) i) x

private noncomputable def ambientMatrixCoordinate
    (row column : b.support ⊕ ι) :
    Variety.PolynomialFunction (RootCurveAmbient (b := b) (ι := ι) (k := k)) :=
  generalLinearMatrixCoordinate
    (Module.finrank k (SpecializedCarrier (b := b) (ι := ι) (k := k)))
    (carrierIndexEquiv (b := b) (ι := ι) (k := k) row)
    (carrierIndexEquiv (b := b) (ι := ι) (k := k) column)

omit [IsAlgClosed k] in
private lemma ambientMatrixCoordinate_rootMorphism_apply
    (i : ι) (row column : b.support ⊕ ι) (x : Variety.Point (KPlus k)) :
    ambientMatrixCoordinate (b := b) (ι := ι) (k := k) row column
        ((rootMorphism (P := P) (b := b) i).onPoints x) =
      canonicalRootCurveMatrix (P := P) (b := b) i (x.val PUnit.unit) row column := by
  change generalLinearMatrixCoordinate
      (Module.finrank k (SpecializedCarrier (b := b) (ι := ι) (k := k)))
      (carrierIndexEquiv (b := b) (ι := ι) (k := k) row)
      (carrierIndexEquiv (b := b) (ι := ι) (k := k) column)
      ((rootMorphism (P := P) (b := b) i).onPoints x) = _
  rw [generalLinearMatrixCoordinate_apply, rootMorphism_apply,
    generalLinearRepresentationPoint_matrix]
  simp [rootPointRepresentation, carrierBasis, Module.Basis.reindex_apply]
  rfl

private def rootRecoveryCoefficient (i : ι)
    (p q : b.support ⊕ ι) : k :=
  specializeMatrix (S := k)
      (titsWordInv (P := P) (rootRecoveryWord (P := P) (b := b) i))
      (Sum.inl (rootRecoverySimple (P := P) (b := b) i)) p *
    specializeMatrix (S := k)
      (titsWord (P := P) (rootRecoveryWord (P := P) (b := b) i))
      q (rootRecoveryColumn (P := P) (b := b) i)

private noncomputable def rootRecoveryFunction (i : ι) :
    Variety.PolynomialFunction (RootCurveAmbient (b := b) (ι := ι) (k := k)) :=
  ∑ q, ∑ p,
    algebraMap k (Variety.PolynomialFunction
      (RootCurveAmbient (b := b) (ι := ι) (k := k)))
        (rootRecoveryCoefficient (P := P) (b := b) i p q) *
      ambientMatrixCoordinate (b := b) (ι := ι) (k := k) p q

omit [IsAlgClosed k] in
private lemma rootRecoveryFunction_rootMorphism_apply
    (i : ι) (x : Variety.Point (KPlus k)) :
    rootRecoveryFunction (P := P) (b := b) i
        ((rootMorphism (P := P) (b := b) i).onPoints x) =
      x.val PUnit.unit := by
  classical
  change (Variety.PolynomialFunction.evalAlgHom
    (RootCurveAmbient (b := b) (ι := ι) (k := k))
    ((rootMorphism (P := P) (b := b) i).onPoints x))
      (rootRecoveryFunction (P := P) (b := b) i) = x.val PUnit.unit
  rw [rootRecoveryFunction, map_sum]
  simp_rw [map_sum, map_mul, AlgHom.commutes]
  change (∑ q, ∑ p,
    rootRecoveryCoefficient (P := P) (b := b) i p q *
      ambientMatrixCoordinate (b := b) (ι := ι) (k := k) p q
        ((rootMorphism (P := P) (b := b) i).onPoints x)) = x.val PUnit.unit
  simp_rw [ambientMatrixCoordinate_rootMorphism_apply]
  conv_rhs =>
    rw [← rootRecoveryValue_rootCurveMatrix (P := P) (b := b) i (x.val PUnit.unit)]
  simp only [rootRecoveryValue, rootRecoveryCoefficient, Matrix.mul_apply,
    Finset.sum_mul, canonicalRootCurveMatrix]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  ring

omit [IsAlgClosed k] in
/-- Every specialized integral root curve is injective in its additive parameter. -/
theorem rootMorphism_injective (i : ι) :
    Function.Injective (rootMorphism (P := P) (b := b) (k := k) i).onPoints := by
  intro x y hxy
  apply (additiveGroupPointEquiv k).injective
  change x.val PUnit.unit = y.val PUnit.unit
  rw [← rootRecoveryFunction_rootMorphism_apply (P := P) (b := b) i x,
    ← rootRecoveryFunction_rootMorphism_apply (P := P) (b := b) i y, hxy]

omit [IsAlgClosed k] in
/-- The recovery polynomial supplies every affine-line coordinate on the root curve. -/
theorem rootMorphism_coordinate_preimage (i : ι) :
    ∀ c : (KPlus k).Coordinates,
      ∃ q : Variety.PolynomialFunction
          (RootCurveAmbient (b := b) (ι := ι) (k := k)),
        Variety.PolynomialFunction.pullback
            (rootMorphism (P := P) (b := b) i).toVariety q =
          Variety.PolynomialFunction.ofPolynomial (KPlus k) (MvPolynomial.X c) := by
  intro c
  refine ⟨rootRecoveryFunction (P := P) (b := b) i, ?_⟩
  apply Variety.PolynomialFunction.ext
  intro x
  change rootRecoveryFunction (P := P) (b := b) i
      ((rootMorphism (P := P) (b := b) i).onPoints x) =
    evalPolynomial x.val (MvPolynomial.X c)
  rw [rootRecoveryFunction_rootMorphism_apply, evalPolynomial_X]

/-- The closed subgroup which is the image of the root morphism. -/
noncomputable def rootSubgroup (i : ι) :
    ClosedSubgroup (RootCurveAmbient (b := b) (ι := ι) (k := k)) :=
  (rootMorphism (P := P) (b := b) (k := k) i).imageClosedSubgroup

/-- The canonical additive parametrization of the closed root subgroup. -/
noncomputable def rootParametrization (i : ι) :
    @OneParameterParametrization k _
      (rootSubgroup (P := P) (b := b) (k := k) i).carrierVariety
      (rootSubgroup (P := P) (b := b) (k := k) i).carrierAlgebraicGroup :=
  Classical.choose
    ((rootMorphism (P := P) (b := b) i).iso_imageClosedSubgroup_of_coordinate_preimage
      (rootMorphism_injective (P := P) (b := b) i)
      (rootMorphism_coordinate_preimage (P := P) (b := b) i))

/-- Each root image is a closed one-parameter subgroup. -/
theorem rootSubgroup_isOneParameter (i : ι) :
    @IsOneParameterGroup k _
      (rootSubgroup (P := P) (b := b) (k := k) i).carrierVariety
      (rootSubgroup (P := P) (b := b) (k := k) i).carrierAlgebraicGroup :=
  ⟨rootParametrization (P := P) (b := b) i⟩

theorem rootParametrization_hom (i : ι) :
    @AlgebraicGroup.Iso.hom k _ (KPlus k)
        (rootSubgroup (P := P) (b := b) (k := k) i).carrierVariety
        (inferInstance : AlgebraicGroup (KPlus k))
        (rootSubgroup (P := P) (b := b) (k := k) i).carrierAlgebraicGroup
        (rootParametrization (P := P) (b := b) i) =
      (rootMorphism (P := P) (b := b) i).codRestrictClosedSubgroup
        (rootSubgroup (P := P) (b := b) (k := k) i) (fun y => ⟨y, rfl⟩) :=
  Classical.choose_spec
    ((rootMorphism (P := P) (b := b) i).iso_imageClosedSubgroup_of_coordinate_preimage
      (rootMorphism_injective (P := P) (b := b) i)
      (rootMorphism_coordinate_preimage (P := P) (b := b) i))

theorem rootParametrization_include_value (i : ι) (a : k) :
    (rootSubgroup (P := P) (b := b) (k := k) i).includePoint
        (@OneParameterParametrization.value k _
          (rootSubgroup (P := P) (b := b) (k := k) i).carrierVariety
          (rootSubgroup (P := P) (b := b) (k := k) i).carrierAlgebraicGroup
          (rootParametrization (P := P) (b := b) i) a) =
      (rootMorphism (P := P) (b := b) i).onPoints (kPlusPoint a) := by
  let _ : AlgebraicGroup
      (rootSubgroup (P := P) (b := b) (k := k) i).carrierVariety :=
    (rootSubgroup (P := P) (b := b) (k := k) i).carrierAlgebraicGroup
  change (rootSubgroup (P := P) (b := b) (k := k) i).inclusion.onPoints
      ((@AlgebraicGroup.Iso.hom k _ (KPlus k)
          (rootSubgroup (P := P) (b := b) (k := k) i).carrierVariety
          (inferInstance : AlgebraicGroup (KPlus k))
          (rootSubgroup (P := P) (b := b) (k := k) i).carrierAlgebraicGroup
          (rootParametrization (P := P) (b := b) i)).onPoints (kPlusPoint a)) = _
  rw [rootParametrization_hom]
  exact (rootMorphism (P := P) (b := b) i).codRestrictClosedSubgroup_inclusion_apply
    (rootSubgroup (P := P) (b := b) (k := k) i) (fun y => ⟨y, rfl⟩) (kPlusPoint a)

/-- The globally indexed regular family, ready to provide the `x` field of Chevalley data. -/
noncomputable def rootMorphismFamily : ι →
    AlgebraicGroup.Morphism (KPlus k)
      (RootCurveAmbient (b := b) (ι := ι) (k := k)) :=
  fun i => rootMorphism (P := P) (b := b) i

/-- The point-valued root element obtained from the global regular family. -/
noncomputable def rootElement (i : ι) (t : k) :
    Variety.Point (RootCurveAmbient (b := b) (ι := ι) (k := k)) :=
  (rootMorphismFamily (P := P) (b := b) i).onPoints (kPlusPoint t)

omit [IsAlgClosed k] in
theorem rootElement_add (i : ι) (s t : k) :
    rootElement (P := P) (b := b) i s * rootElement (P := P) (b := b) i t =
      rootElement (P := P) (b := b) i (s + t) := by
  rw [rootElement, rootElement, rootElement, ← map_mul, kPlusPoint_mul]

omit [IsAlgClosed k] in
theorem rootElement_injective (i : ι) :
    Function.Injective (rootElement (P := P) (b := b) (k := k) i) := by
  intro s t hst
  have hpoint := rootMorphism_injective (P := P) (b := b) i hst
  have hcoord := congrArg
    (fun x : Variety.Point (KPlus k) =>
      Multiplicative.toAdd (additiveGroupPointEquiv k x)) hpoint
  simpa [kPlusPoint] using hcoord

/-- The normalizer element with the convention used by `IsChevalleySystem`. -/
noncomputable def rootNElement (i : ι) (t : kˣ) :
    Variety.Point (RootCurveAmbient (b := b) (ι := ι) (k := k)) := by
  letI := P.indexNeg
  exact rootElement (P := P) (b := b) i (t : k) *
    rootElement (P := P) (b := b) (-i) (-((t : k)⁻¹)) *
    rootElement (P := P) (b := b) i (t : k)

/-- The coroot element, using `h_alpha(t) = n_alpha(1)⁻¹ n_alpha(t)`. -/
noncomputable def rootHElement (i : ι) (t : kˣ) :
    Variety.Point (RootCurveAmbient (b := b) (ι := ι) (k := k)) :=
  (rootNElement (P := P) (b := b) i 1)⁻¹ *
    rootNElement (P := P) (b := b) i t

omit [IsAlgClosed k] in
theorem rootNElement_formula (i : ι) (t : kˣ) :
    letI := P.indexNeg
    rootNElement (P := P) (b := b) i t =
      rootElement (P := P) (b := b) i (t : k) *
        rootElement (P := P) (b := b) (-i) (-((t : k)⁻¹)) *
        rootElement (P := P) (b := b) i (t : k) := by
  rfl

omit [IsAlgClosed k] in
theorem rootHElement_formula (i : ι) (t : kˣ) :
    rootHElement (P := P) (b := b) i t =
      (rootNElement (P := P) (b := b) i 1)⁻¹ *
        rootNElement (P := P) (b := b) i t :=
  rfl

/-- The lower transvection in the standard rank-one representation. -/
def standardNegativeRootUnit (t : k) : Matrix.GeneralLinearGroup (Fin 2) k :=
  ⟨!![1, 0; t, 1], !![1, 0; -t, 1], by
    simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

/-- The standard rank-one normalizer element, with the repository's root-factor order. -/
def standardRankOneNUnit (t : kˣ) : Matrix.GeneralLinearGroup (Fin 2) k :=
  Matrix.GeneralLinearGroup.upperRightHom (t : k) *
    standardNegativeRootUnit (-((t : k)⁻¹)) *
    Matrix.GeneralLinearGroup.upperRightHom (t : k)

/-- The standard rank-one coroot element in the repository's `h` convention. -/
def standardRankOneHUnit (t : kˣ) : Matrix.GeneralLinearGroup (Fin 2) k :=
  (standardRankOneNUnit (1 : kˣ))⁻¹ * standardRankOneNUnit t

omit [IsAlgClosed k] in
/-- Exact rank-one matrix formula for the chosen `n_alpha` convention. -/
theorem standardRankOneNUnit_matrix (t : kˣ) :
    ((standardRankOneNUnit t : Matrix.GeneralLinearGroup (Fin 2) k) :
        Matrix (Fin 2) (Fin 2) k) =
      !![0, (t : k); -((t : k)⁻¹), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [standardRankOneNUnit, standardNegativeRootUnit,
      Matrix.GeneralLinearGroup.upperRightHom, Matrix.mul_apply, Fin.sum_univ_two]

omit [IsAlgClosed k] in
/-- Exact rank-one matrix formula for `h_alpha(t) = n_alpha(1)⁻¹ n_alpha(t)`. -/
theorem standardRankOneHUnit_matrix (t : kˣ) :
    ((standardRankOneHUnit t : Matrix.GeneralLinearGroup (Fin 2) k) :
        Matrix (Fin 2) (Fin 2) k) =
      !![((t : k)⁻¹), 0; 0, (t : k)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [standardRankOneHUnit, standardRankOneNUnit, standardNegativeRootUnit,
      Matrix.GeneralLinearGroup.upperRightHom, Matrix.mul_apply, Fin.sum_univ_two]

/-- The global family is injective and its image consists of closed one-parameter subgroups. -/
theorem characteristicFreeRootCurves :
    (∀ i, Function.Injective
      (rootMorphismFamily (P := P) (b := b) (k := k) i).onPoints) ∧
    (∀ i, @IsOneParameterGroup k _
      (rootSubgroup (P := P) (b := b) (k := k) i).carrierVariety
      (rootSubgroup (P := P) (b := b) (k := k) i).carrierAlgebraicGroup) := by
  exact ⟨fun i => rootMorphism_injective (P := P) (b := b) i,
    fun i => rootSubgroup_isOneParameter (P := P) (b := b) i⟩

end

end

end RootPairing.IntegralGeckConstruction
