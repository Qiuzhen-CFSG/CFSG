module

public import Theory.AlgebraicGroup.RootSystems.IntegralAllRootOperators
public import Mathlib.Algebra.Ring.NegOnePow

/-!
# Integral opposition and the signs of Tits words

Opposition exchanges raising and lowering operators, but it does not commute
with an integral Tits word. The correction on a root is the product of the
word's signs on that root and its negative. Root-string theory identifies each
simple correction with the parity of a Cartan integer. It is therefore
multiplicative when roots add.

The resulting diagonal correction conjugates a simple lowering operator by
its root's correction sign. This proves the signed opposition formula for
transported operators along an arbitrary word, including the literal canonical
routes used by the F4 adjoint map in the parent module.

Sources: the root-string and Tits-word formulas of `IntegralGeckConstruction`,
the transported operators of `IntegralAllRootOperators`, and GLS3 §§2.2–2.6.
-/

@[expose] public section

open scoped Matrix
open RootPairing
namespace RootPairing.IntegralGeckConstruction
set_option linter.unusedSectionVars false
noncomputable section
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

/-- The two opposite root-string signs multiply to the parity of the Cartan integer. -/
lemma opposition_chain_sign_eq_pairing (i j : ι) :
    let := P.indexNeg
    (-1 : ℤ) ^ P.chainBotCoeff i j * (-1 : ℤ) ^ P.chainBotCoeff i (-j) =
      (P.pairingIn ℤ j i).negOnePow := by
  let := P.indexNeg
  dsimp only
  have hn : P.chainBotCoeff i (-j) = P.chainTopCoeff i j :=
    P.chainBotCoeff_reflectionPerm_right (i := i) (j := j)
  rw [hn]
  by_cases hlin : LinearIndependent R ![P.root i, P.root j]
  · rw [← P.chainBotCoeff_sub_chainTopCoeff hlin, Int.negOnePow_sub,
      Units.val_mul, Int.coe_negOnePow_natCast, Int.coe_negOnePow_natCast]
  · rw [P.chainBotCoeff_of_not_linearIndependent hlin,
      P.chainTopCoeff_of_not_linearIndependent hlin]
    rcases IsReduced.eq_or_eq_neg (P := P) i j hlin with he | he
    · have hij := P.root.injective he
      subst j
      simp [Int.negOnePow_even 2 (by decide)]
    · have hij : j = -i := P.root.injective (by
        rw [show P.root (-i) = -P.root i by simp, he, neg_neg])
      subst j
      simp [Int.negOnePow_neg, Int.negOnePow_even 2 (by decide)]

/-- The correction to commuting opposition past an integral Tits word on a root line. -/
def titsWordOppositionSign (w : List b.support) (j : ι) : ℤ :=
  let := P.indexNeg
  titsWordSign w j * titsWordSign w (-j)

/-- Each additional reflection contributes the parity of its Cartan integer. -/
lemma titsWordOppositionSign_cons (i : b.support) (w : List b.support) (j : ι) :
    titsWordOppositionSign (i :: w) j = titsWordOppositionSign w j *
      ((P.pairingIn ℤ (reflectionWord w j) i).negOnePow : ℤ) := by
  let := P.indexNeg
  simp only [titsWordOppositionSign, titsWordSign, reflectionWord_neg]
  rw [mul_mul_mul_comm, opposition_chain_sign_eq_pairing]

/-- The opposition correction is multiplicative on every root sum. -/
lemma titsWordOppositionSign_root_add (w : List b.support) {i j k : ι}
    (h : P.root k = P.root i + P.root j) :
    titsWordOppositionSign w k = titsWordOppositionSign w i * titsWordOppositionSign w j := by
  induction w with
  | nil => simp [titsWordOppositionSign, titsWordSign]
  | cons a w ih =>
    rw [titsWordOppositionSign_cons, titsWordOppositionSign_cons,
      titsWordOppositionSign_cons, ih]
    have hr : P.root (reflectionWord w k) =
        P.root (reflectionWord w i) + P.root (reflectionWord w j) := by
      simp only [root_reflectionWord, h, smul_add]
    rw [P.pairingIn_eq_add_of_root_eq_add (S := ℤ) hr, Int.negOnePow_add, Units.val_mul]
    ring

/-- Every integral carrier sign is an involutive scalar. -/
lemma titsWordSign_mul_self_opposition (w : List b.support) (j : ι) :
    titsWordSign (P := P) w j * titsWordSign w j = 1 := by
  induction w with
  | nil => simp [titsWordSign]
  | cons i w ih =>
      simp only [titsWordSign]
      rw [mul_mul_mul_comm, ih]
      simp [← pow_add, ← two_mul]

/-- Opposite root lines have the same opposition correction. -/
lemma titsWordOppositionSign_neg (w : List b.support) (j : ι) :
    let := P.indexNeg
    titsWordOppositionSign w (-j) = titsWordOppositionSign w j := by
  let := P.indexNeg
  simp only [titsWordOppositionSign, neg_neg, mul_comm]

/-- The opposition correction is an involutive scalar. -/
lemma titsWordOppositionSign_mul_self (w : List b.support) (j : ι) :
    titsWordOppositionSign (P := P) w j * titsWordOppositionSign w j = 1 := by
  let := P.indexNeg
  simp only [titsWordOppositionSign]
  rw [mul_mul_mul_comm, titsWordSign_mul_self_opposition, titsWordSign_mul_self_opposition, one_mul]

/-- The correction fixes Cartan coordinates and scales each root by its opposition sign. -/
def titsWordOppositionDiagonal (w : List b.support) : Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ :=
  Matrix.diagonal (Sum.elim (fun _ => 1) (titsWordOppositionSign w))

/-- The word correction fixes Cartan basis vectors. -/
lemma titsWordOppositionDiagonal_mulVec_u (w : List b.support) (j : b.support) :
    titsWordOppositionDiagonal w *ᵥ u j = u j := by
  ext (i | i) <;> simp [titsWordOppositionDiagonal, u, Pi.single_apply]

/-- The word correction acts by its specified scalar on root basis vectors. -/
lemma titsWordOppositionDiagonal_mulVec_v (w : List b.support) (j : ι) :
    titsWordOppositionDiagonal w *ᵥ v (b := b) j = titsWordOppositionSign w j • v (b := b) j := by
  ext (i | i)
  · simp [titsWordOppositionDiagonal, v]
  · by_cases h : i = j
    · subst i; simp [titsWordOppositionDiagonal, v]
    · simp [titsWordOppositionDiagonal, v, h]

/-- The diagonal correction is an involution. -/
lemma titsWordOppositionDiagonal_sq (w : List b.support) :
    titsWordOppositionDiagonal (P := P) w * titsWordOppositionDiagonal w = 1 := by
  rw [titsWordOppositionDiagonal, Matrix.diagonal_mul_diagonal]
  have hh : (fun j : b.support ⊕ ι =>
      Sum.elim (fun _ => 1) (titsWordOppositionSign (P := P) w) j *
      Sum.elim (fun _ => 1) (titsWordOppositionSign (P := P) w) j) = fun _ => 1 := by
    funext j
    cases j <;> simp [titsWordOppositionSign_mul_self]
  rw [hh, Matrix.diagonal_one]

/-- Conjugating a lowering operator by the correction gives the sign of its simple root. -/
lemma titsWordOppositionDiagonal_mul_fMatrix (w : List b.support) (i : b.support) :
    titsWordOppositionDiagonal w * fMatrix (P := P) i =
      titsWordOppositionSign w i • (fMatrix i * titsWordOppositionDiagonal w) := by
  let := P.indexNeg
  ext (j | j) (k | k)
  · simp [titsWordOppositionDiagonal, fMatrix]
  · simp only [titsWordOppositionDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.smul_apply,
      fMatrix, Matrix.fromBlocks_apply₁₂, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
      smul_eq_mul, one_mul]
    split_ifs with h
    · rcases h with ⟨rfl, rfl⟩
      simp [titsWordOppositionSign_mul_self]
    · simp
  · simp only [titsWordOppositionDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.smul_apply,
      fMatrix, Matrix.fromBlocks_apply₂₁, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
      smul_eq_mul, mul_one]
    split_ifs with h
    · subst j
      rw [titsWordOppositionSign_neg]
    · simp
  · simp only [titsWordOppositionDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.smul_apply,
      fMatrix, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Sum.elim_inr, smul_eq_mul]
    split_ifs with h
    · have hh : P.root j = P.root (-i) + P.root k := by simp [h]; abel
      rw [titsWordOppositionSign_root_add w hh, titsWordOppositionSign_neg]
      ring
    · simp

/-- The Cartan sublattice remains fixed by opposition after applying any Tits word. -/
lemma omegaMatrix_mulVec_titsWord_u (w : List b.support) (j : b.support) :
    omegaMatrix *ᵥ (titsWord (P := P) w *ᵥ u j) = titsWord w *ᵥ u j := by
  induction w using List.reverseRecOn generalizing j with
  | nil => simp only [titsWord, Matrix.one_mulVec, omegaMatrix_mulVec_u]
  | append_singleton w i ih =>
      rw [titsWord_append]
      simp only [titsWord, mul_one, ← Matrix.mulVec_mulVec, titsLift_mulVec_u,
        Matrix.mulVec_sub, Matrix.mulVec_smul, ih]

/-- Integral opposition commutes past a Tits word with its necessary diagonal correction. -/
lemma omegaMatrix_mul_titsWord (w : List b.support) :
    omegaMatrix * titsWord (P := P) w = titsWord w * titsWordOppositionDiagonal w * omegaMatrix := by
  let := P.indexNeg
  apply Matrix.ext_of_mulVec_single
  rintro (j | j)
  · change _ *ᵥ u j = _ *ᵥ u j
    simp only [← Matrix.mulVec_mulVec, omegaMatrix_mulVec_u, titsWordOppositionDiagonal_mulVec_u,
      omegaMatrix_mulVec_titsWord_u]
  · change _ *ᵥ v j = _ *ᵥ v j
    simp only [← Matrix.mulVec_mulVec, omegaMatrix_mulVec_v, titsWord_mulVec_v,
      Matrix.mulVec_smul, titsWordOppositionDiagonal_mulVec_v, reflectionWord_neg, smul_smul,
      titsWordOppositionSign, neg_neg]
    rw [mul_comm (titsWordSign w (-j)) (titsWordSign w j),
      mul_assoc, titsWordSign_mul_self_opposition, mul_one]

/-- The inverse word has the corresponding integral opposition correction. -/
lemma omegaMatrix_conj_titsWordInv (w : List b.support) :
    omegaMatrix * titsWordInv (P := P) w * omegaMatrix =
      titsWordOppositionDiagonal w * titsWordInv w := by
  calc
    _ = (titsWordOppositionDiagonal w * titsWordOppositionDiagonal w) *
        (omegaMatrix * titsWordInv w * omegaMatrix) := by rw [titsWordOppositionDiagonal_sq, one_mul]
    _ = titsWordOppositionDiagonal w * (titsWordInv w * titsWord w) * titsWordOppositionDiagonal w *
        omegaMatrix * titsWordInv w * omegaMatrix := by
      rw [titsWord_inv_mul, mul_one]
      simp only [mul_assoc]
    _ = titsWordOppositionDiagonal w * titsWordInv w *
        (titsWord w * titsWordOppositionDiagonal w * omegaMatrix) * titsWordInv w * omegaMatrix := by simp only [mul_assoc]
    _ = titsWordOppositionDiagonal w * titsWordInv w * (omegaMatrix * titsWord w) *
        titsWordInv w * omegaMatrix := by rw [← omegaMatrix_mul_titsWord]
    _ = titsWordOppositionDiagonal w * titsWordInv w * omegaMatrix *
        (titsWord w * titsWordInv w) * omegaMatrix := by simp only [mul_assoc]
    _ = _ := by rw [titsWord_mul_inv, mul_one, mul_assoc, omegaMatrix_sq, mul_one]

/-- Opposition exchanges transported raising and lowering operators with the product of
the two carrier signs. This applies to the literal canonical routes in the parent module. -/
lemma omegaMatrix_conj_transported_eMatrix (w : List b.support) (i : b.support) :
    omegaMatrix * transportedMatrix w (eMatrix (P := P) i) * omegaMatrix =
      titsWordOppositionSign w i • transportedMatrix w (fMatrix i) := by
  calc
    _ = titsWord w * titsWordOppositionDiagonal w * fMatrix i *
        (omegaMatrix * titsWordInv w * omegaMatrix) := by
      simp only [transportedMatrix, ← mul_assoc]
      rw [omegaMatrix_mul_titsWord]
      simp only [mul_assoc, omegaMatrix_mul_eMatrix]
    _ = titsWord w * (titsWordOppositionDiagonal w * fMatrix i) *
        titsWordOppositionDiagonal w * titsWordInv w := by
      rw [omegaMatrix_conj_titsWordInv]
      simp only [mul_assoc]
    _ = _ := by
      rw [titsWordOppositionDiagonal_mul_fMatrix]
      simp only [Matrix.mul_smul, Matrix.smul_mul, mul_assoc, titsWordOppositionDiagonal_sq,
        mul_one, transportedMatrix]

end
end RootPairing.IntegralGeckConstruction
