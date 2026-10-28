module

public import Theory.SpecificGroups.LieType.TheoremDRootNormalizer.CorootTorus

/-!
# Coroot words at cubic units

The simple coroot word has the inverse diagonal parameter convention. The
Tits grading proves this identity at every square over an arbitrary field.
A unit of cube one satisfies `u⁻¹ = u²`, so this suffices for the E6 central
parameters in every characteristic, without a square-root hypothesis.

The grading calculation is adapted from `TheoremDRootNormalizer.CorootTorus`;
its final theorem there uses finite characteristic two. Here the consumer is
the central coroot family in E6, E7 and E8, including characteristic three.
Source: Steinberg, *Lectures on Chevalley Groups*, Theorem 1 and Lemmas 5–6;
GLS3 §§1.12 and 2.5 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section

open RootPairing.IntegralGeckConstruction
open ExceptionalSplit.TheoremDRootNormalizer
namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CorootMatrices

variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]
  {F : Type*} [Field F]

private abbrev rootCurve (r : ι) (t : F) :=
  rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) r t

private abbrev diag (i : b.support) (u : Fˣ) :=
  integralChevalleyTorusElement (P := P)
    (integralChevalleySimpleCorootParameter i u)

private theorem diag_tits (i : b.support) (u : Fˣ) :
    rootCurveTitsWord (P := P) (S := F) [i] * diag (P := P) i u =
      (diag (P := P) i u)⁻¹ * rootCurveTitsWord (P := P) (S := F)
        [i] := by
  apply Units.ext
  change specializeMatrix (titsWord [i]) * Matrix.diagonal _ =
    Matrix.diagonal _ * specializeMatrix (titsWord [i])
  simp only [titsWord, Matrix.mul_one]
  ext row col
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hz : titsLift i row col = 0
  · simp [specializeMatrix, hz]
  · have hw := titsLift_respectsChevalleyGrading (P := P) i
      row col hz (i : ι)
    have hn : chevalleyBasisWeight (P := P) row (i : ι) =
        -chevalleyBasisWeight (P := P) col (i : ι) := by
      rw [hw]
      cases col with
      | inl j => simp [chevalleyBasisWeight]
      | inr j =>
        exact P.pairingIn_reflectionPerm_self_right ℤ j _
    have heval (a : b.support ⊕ ι) :
        chevalleyBasisTorusUnit (P := P)
          (integralChevalleySimpleCorootParameter i u) a =
        u ^ (-chevalleyBasisWeight (P := P) a (i : ι)) := by
      unfold chevalleyBasisTorusUnit integralChevalleySimpleCorootParameter
      rw [Finset.prod_eq_single i]
      · simp only [if_true]
      · intro j _ hj
        simp [hj]
      · simp
    have hu : chevalleyBasisTorusUnit (P := P)
        (integralChevalleySimpleCorootParameter i u) col =
        (chevalleyBasisTorusUnit (P := P)
        (integralChevalleySimpleCorootParameter i u) row)⁻¹ := by
      rw [heval, heval, hn]
      simp

    rw [hu]
    exact mul_comm _ _

private theorem diag_root (i : b.support) (u : Fˣ)
    (r : ι) (t : F) :
    (diag (P := P) i u)⁻¹ * rootCurve (b := b) r t * diag (P := P) i u =
      rootCurve (b := b) r
        (((u ^ P.pairingIn ℤ r (i : ι) :
          Fˣ) : F) * t) := by
  exact integralChevalleyRootCurve_simpleCoroot_conjugation
    i u r t

private theorem diag_mul (i : b.support) (u v : Fˣ) :
    diag (P := P) i (u * v) = diag (P := P) i u * diag (P := P) i v := by
  rw [diag, ← integralChevalleyTorusElement_mul]
  congr 1
  funext j
  simp only [integralChevalleySimpleCorootParameter, Pi.mul_apply]
  split_ifs <;> simp

private theorem matrixN_square (i : b.support) (u : Fˣ) :
    (matrixN (b := b) (F := F) (i : ι) (u ^ 2)) =
      (diag (P := P) i u)⁻¹ * (matrixN (b := b) (F := F) (i : ι) 1) * diag (P := P) i u := by
  let := P.indexNeg
  change rootCurve (b := b) _ _ * rootCurve (b := b) _ _ *
    rootCurve (b := b) _ _ =
    (diag (P := P) i u)⁻¹ * (rootCurve (b := b) _ 1 * rootCurve (b := b) _ (-1⁻¹) *
    rootCurve (b := b) _ 1) * diag (P := P) i u
  symm
  calc
    _ = ((diag (P := P) i u)⁻¹ * rootCurve (b := b) (i : ι) 1 * diag (P := P) i u) *
        ((diag (P := P) i u)⁻¹ * rootCurve (b := b) (-(i : ι)) (-1⁻¹) * diag (P := P) i u) *
        ((diag (P := P) i u)⁻¹ * rootCurve (b := b) (i : ι) 1 * diag (P := P) i u) := by group
    _ = _ := by
      rw [diag_root, diag_root]
      simp

private theorem torus_square (i : b.support) (u : Fˣ) :
    (matrixH (b := b) (F := F) (i : ι) (u ^ 2)) = (diag (P := P) i (u ^ 2))⁻¹ := by
  change (matrixN (b := b) (F := F) _ (u ^ 2)) * (matrixN (b := b) (F := F) _ (-1)) = _
  rw [matrixN_square, matrixN_neg_one]
  rw [matrixN_one, mul_assoc (diag (P := P) i u)⁻¹, diag_tits]
  rw [pow_two, diag_mul, mul_inv_rev]
  group

/-- The rank-one word identity on squares, over any field. -/
theorem matrixH_square (i : b.support) (u : Fˣ) :
    matrixH (b := b) (F := F) i (u ^ 2) =
      integralChevalleyTorusElement (P := P)
        (integralChevalleySimpleCorootParameter i (u ^ 2)⁻¹) := by
  rw [torus_square]
  rw [diag, ← integralChevalleyTorusElement_inv]
  congr 1
  funext j
  simp only [integralChevalleySimpleCorootParameter, Pi.inv_apply]
  split_ifs <;> simp

/-- At a cubic unit, the word with input `u⁻¹` realizes parameter `u`. -/
theorem matrixH_inv_of_cube (i : b.support) (u : Fˣ) (hu : u ^ 3 = 1) :
    matrixH (b := b) (F := F) i (↑u⁻¹) =
      integralChevalleyTorusElement (P := P)
        (integralChevalleySimpleCorootParameter i u) := by
  have hs : u ^ 2 = u⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa only [← pow_succ] using hu
  rw [← hs, Units.val_pow_eq_pow_val, matrixH_square, hs, inv_inv]

end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CorootMatrices
