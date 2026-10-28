module

public import Theory.SpecificGroups.LieType.ExceptionalSplitModels
public import Theory.AlgebraicGroup.Borel.IntegralChevalleyTorusConjugation
public import Theory.AlgebraicGroup.RootSystems.IntegralRootCurveSimpleGeneration
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Coroot tori in finite binary Chevalley groups

A simple coroot diagonal is an explicit six-root word. The Tits grading
proves the identity on squares, and Frobenius supplies square roots over
finite fields of characteristic two. Multiplication then places the entire
coroot torus in the literal all-root-generated matrix group.

This generalizes the calculation in `F4ChevalleyCorootWords` to every finite
reduced crystallographic pairing; no algebraically closed field or alternate
carrier is used. A simple-root matrix entry also recovers its parameter.

Sources: Steinberg, *Lectures on Chevalley Groups*, Theorem 1 and Lemmas 5–6;
Aschbacher–Smith A.2.18, printed p.40 (the torus obstruction).
-/

@[expose] public section

open RootPairing.IntegralGeckConstruction
noncomputable section
namespace ExceptionalSplit.TheoremDRootNormalizer
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]
  {F : Type*} [Field F]

private abbrev rootCurve (r : ι) (t : F) :=
  rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) r t

def matrixN (r : ι) (t : F) : (Matrix (b.support ⊕ ι) (b.support ⊕ ι) F)ˣ :=
  let := P.indexNeg
  rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) r t *
    rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) (-r) (-t⁻¹) *
    rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) r t

def matrixH (r : ι) (t : F) : (Matrix (b.support ⊕ ι) (b.support ⊕ ι) F)ˣ :=
  matrixN (b := b) r t * matrixN (b := b) (F := F) r (-1)

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

theorem matrixN_one (i : b.support) :
    (matrixN (b := b) (F := F) (i : ι) 1) =
      rootCurveTitsWord (P := P) (S := F) [i] := by
  let := P.indexNeg
  rw [rootCurveTitsWord_cons, rootCurveTitsWord_nil, mul_one]
  change rootCurve (b := b) _ 1 * rootCurve (b := b) _ (-1⁻¹) *
    rootCurve (b := b) _ 1 = _
  simp only [rootCurve,
    rootCurveUnit_simple, rootCurveUnit_neg_simple,
    inv_one]

theorem matrixN_neg_one (i : b.support) :
    matrixN (b := b) (F := F) (i : ι) (-1) =
      (matrixN (b := b) (F := F) (i : ι) 1)⁻¹ := by
  let := P.indexNeg
  change rootCurve (b := b) _ (-1) * rootCurve (b := b) _ (-(-1)⁻¹) *
      rootCurve (b := b) _ (-1) =
    (rootCurve (b := b) _ 1 * rootCurve (b := b) _ (-1⁻¹) *
      rootCurve (b := b) _ 1)⁻¹
  simp [rootCurve, mul_inv_rev, rootCurveUnit_inv, mul_assoc]

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

private theorem unit_square_surjective [Finite F] [CharP F 2] (t : Fˣ) :
    ∃ u : Fˣ, u ^ 2 = t := by
  obtain ⟨a, ha⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) (t : F)
  have hane : a ≠ 0 := by
    intro hz
    apply t.ne_zero
    simpa only [hz, mul_zero] using ha
  refine ⟨Units.mk0 a hane, ?_⟩
  apply Units.ext
  change a ^ 2 = (t : F)
  simpa only [pow_two] using ha.symm

/-- The coroot word uses the inverse of the diagonal parameter convention. -/
theorem matrixH_simple [Finite F] [CharP F 2] (i : b.support)
    (t : Fˣ) :
    (matrixH (b := b) (F := F) i t) = integralChevalleyTorusElement (P := P)
      (integralChevalleySimpleCorootParameter i t⁻¹) := by
  obtain ⟨u, rfl⟩ := unit_square_surjective t
  simp only [Units.val_pow_eq_pow_val]
  rw [torus_square]
  change (diag (P := P) i (u ^ 2))⁻¹ = diag (P := P) i ((u ^ 2)⁻¹)
  rw [diag, ← integralChevalleyTorusElement_inv]
  congr 1
  funext j
  simp only [integralChevalleySimpleCorootParameter, Pi.inv_apply]
  split_ifs <;> simp


/-- Every simple-coroot diagonal is a word in the actual root generators. -/
theorem simpleTorus_mem [Finite F] [CharP F 2] (i : b.support) (t : Fˣ) :
    integralChevalleyTorusElement (P := P)
      (integralChevalleySimpleCorootParameter i t) ∈ rootGenerated P b F := by
  rw [← inv_inv t, ← matrixH_simple]
  simp only [matrixH, matrixN]
  repeat first | apply Subgroup.mul_mem | exact root_mem P b F _ _

/-- The diagonal homomorphism on all simple-coroot coordinates. -/
def torusMatrixHom : (b.support → Fˣ) →* (Matrix (b.support ⊕ ι) (b.support ⊕ ι) F)ˣ where
  toFun := integralChevalleyTorusElement (P := P)
  map_one' := integralChevalleyTorusElement_one
  map_mul' := integralChevalleyTorusElement_mul

/-- Over any finite binary field the entire coroot torus belongs to the
literal root-generated carrier. -/
theorem torus_mem [Finite F] [CharP F 2] (u : b.support → Fˣ) :
    integralChevalleyTorusElement (P := P) u ∈ rootGenerated P b F := by
  classical
  have hu : u = ∏ i, integralChevalleySimpleCorootParameter i (u i) := by
    funext j
    simp [integralChevalleySimpleCorootParameter, Finset.prod_apply]
  change u ∈ (rootGenerated P b F).comap (torusMatrixHom (P := P))
  rw [hu]
  apply Subgroup.prod_mem
  intro i _
  exact simpleTorus_mem i (u i)

/-- The distinguished matrix entry recovers a positive simple-root parameter. -/
theorem simpleRoot_entry (i : b.support) (t : F) :
    let := P.indexNeg
    ((rootCurveUnit (integralChevalleyRootOperators (P := P) (b := b)) i t).val)
      (Sum.inl i) (Sum.inr (-i : ι)) = t := by
  let := P.indexNeg
  rw [rootCurveUnit_simple, RootPairing.SimpleGeckGroup.positiveUnit_val,
    RootPairing.SimpleGeckGroup.positiveMatrix_formula]
  simp [eDividedPower, eMatrix]

/-- Simple root parameters are faithful in the original matrix carrier. -/
theorem elementaryRoot_simple_injective (i : b.support) :
    Function.Injective (elementaryRoot P b F i) := by
  let := P.indexNeg
  intro s t h
  have he := congrArg (fun g : rootGenerated P b F =>
    g.val.val (Sum.inl i) (Sum.inr (-i : ι))) h
  simpa only [elementaryRoot, simpleRoot_entry] using he

/-- The coroot torus inside the actual elementary matrix group. -/
def elementaryTorus [Finite F] [CharP F 2] :
    (b.support → Fˣ) →* rootGenerated P b F :=
  (torusMatrixHom (P := P)).codRestrict _ torus_mem

@[simp] theorem elementaryTorus_val [Finite F] [CharP F 2] (u : b.support → Fˣ) :
    (elementaryTorus (P := P) u).val = integralChevalleyTorusElement (P := P) u := rfl

/-- Inverse conjugation has the source's positive root-character exponent. -/
theorem elementaryTorus_conjugation [Finite F] [CharP F 2]
    (u : b.support → Fˣ) (r : ι) (t : F) :
    (elementaryTorus (P := P) u)⁻¹ * elementaryRoot P b F r t *
        elementaryTorus (P := P) u =
      elementaryRoot P b F r ((integralChevalleyRootScale (P := P) u r : F) * t) := by
  apply Subtype.ext
  exact integralChevalleyRootCurve_torus_conjugation u r t

end ExceptionalSplit.TheoremDRootNormalizer
