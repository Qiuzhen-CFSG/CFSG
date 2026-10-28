module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativePointCentralizer.Reference.ScalarQuotient

/-!
# From the native column action to inverse right rows

An explicit nonsingular binary Gram matrix intertwines both original outer
matrix generators with their inverse transposes. Closure under multiplication
extends the identity to the full matrix group. Multiplication by this Gram
matrix is consequently an injective conversion from columns to inverse right
rows, and carries the cubic scalar orbit onto the published row scalar line.

The column vector 1327 becomes row 2045, the published representative with
index 228 and endpoint pair {11,19}. The final lemma applies these identities
to the precise projective membership condition consumed by the reference
binary stabilizer comparison. The endpoint action of the full outer group
and the native quintet comparison remain separate geometric inputs.

Source: Aschbacher--Smith H.12.1(2,5,9), printed pp.393--394, as used in
14.4.12, printed pp.1011--1012 (1 March 2004 manuscript). All finite identities
here are kernel-checked. Reproduction and ATLAS provenance are documented in
Reference/source/README.md; no full matrix-group enumeration is used.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open scoped Matrix

/-- A Gram matrix in the original binary ATLAS coordinates. -/
def referenceGram : Matrix12 := fromRows
  ![2890, 3949, 906, 3751, 32, 3034, 1315, 1324, 3815, 1327, 3018, 1323]

private def gramInverse : Matrix12 := fromRows
  ![1408, 1792, 2560, 2112, 1056, 16, 264, 1025, 2627, 262, 2195, 1292]

private theorem gram_mul_inverse : referenceGram * gramInverse = 1 := by decide +kernel

private theorem gram_C : matrixC.transpose * referenceGram = referenceGram * matrixC := by
  decide +kernel

private theorem gram_D : matrixD.transpose * referenceGram = referenceGram * matrixDInv := by
  decide +kernel

/-- The invariant pairing intertwines columns with inverse right rows for every
member of the full outer extension, including both original generators. -/
theorem referenceGram_intertwines (g : Model) :
    (g.val : Matrix12).transpose * referenceGram = referenceGram * ((g.val⁻¹ : Matrix12ˣ) : Matrix12) := by
  let S : Submonoid Matrix12ˣ :=
    { carrier := {u | (u : Matrix12).transpose * referenceGram =
        referenceGram * (u⁻¹ : Matrix12ˣ).val}
      one_mem' := by simp
      mul_mem' := by
        intro u v hu hv
        change ((u * v : Matrix12ˣ) : Matrix12).transpose * referenceGram =
          referenceGram * ((u * v)⁻¹ : Matrix12ˣ).val
        rw [Units.val_mul, Matrix.transpose_mul, mul_assoc, hu, ← mul_assoc, hv,
          mul_assoc, mul_inv_rev, Units.val_mul] }
  have h : actionGroup.toSubmonoid ≤ S := by
    rw [actionGroup, Subgroup.closure_toSubmonoid_of_finite]
    apply Submonoid.closure_le.mpr
    rintro u (rfl | rfl)
    · exact gram_C
    · exact gram_D
  change g.val ∈ S
  exact h g.property

/-- Convert the literal column module into its right-row realization. -/
def referenceColumnToRow : Space →ₗ[ZMod 2] Space := Matrix.vecMulLinear referenceGram

theorem referenceColumnToRow_injective : Function.Injective referenceColumnToRow := by
  intro v w h
  have hh := congrArg (fun r => Matrix.vecMul r gramInverse) h
  change Matrix.vecMul (Matrix.vecMul v referenceGram) gramInverse =
    Matrix.vecMul (Matrix.vecMul w referenceGram) gramInverse at hh
  simpa only [Matrix.vecMul_vecMul, gram_mul_inverse, Matrix.vecMul_one] using hh

/-- Explicitly retain the inverse in the row-action convention. -/
theorem referenceColumnToRow_action (g : Model) (v : Space) :
    referenceColumnToRow (action g v) =
      Matrix.vecMul (referenceColumnToRow v) ((g.val⁻¹ : Matrix12ˣ) : Matrix12) := by
  change Matrix.vecMul ((g.val : Matrix12) *ᵥ v) referenceGram =
    Matrix.vecMul (Matrix.vecMul v referenceGram) ((g.val⁻¹ : Matrix12ˣ) : Matrix12)
  rw [Matrix.vecMul_mulVec, referenceGram_intertwines, Matrix.vecMul_vecMul]

private theorem gram_scalar : (1 + matrixJ).transpose * referenceGram =
    referenceGram * matrixJ := by decide +kernel

private theorem gram_scalar_sq : matrixJ.transpose * referenceGram =
    referenceGram * (1 + matrixJ) := by decide +kernel

private theorem columnToRow_scalar (v : Space) :
    referenceColumnToRow (action referenceScalar v) =
      Matrix.vecMul (referenceColumnToRow v) matrixJ := by
  change Matrix.vecMul ((scalarUnit : Matrix12) *ᵥ v) referenceGram = _
  rw [coe_scalarUnit, Matrix.vecMul_mulVec, gram_scalar, ← Matrix.vecMul_vecMul]
  rfl

private theorem columnToRow_scalar_sq (v : Space) :
    referenceColumnToRow (action (referenceScalar ^ 2) v) =
      referenceColumnToRow v + Matrix.vecMul (referenceColumnToRow v) matrixJ := by
  rw [action_apply]
  have hz : referenceScalar.val = scalarUnit := rfl
  have he : (referenceScalar ^ 2 : Model).val = scalarUnit ^ 2 := by
    rw [Subgroup.coe_pow, hz]
  rw [he]
  change Matrix.vecMul (((scalarUnit ^ 2 : Matrix12ˣ) : Matrix12) *ᵥ v) referenceGram = _
  rw [coe_scalarUnit_sq, Matrix.vecMul_mulVec, gram_scalar_sq, ← Matrix.vecMul_vecMul,
    Matrix.vecMul_add, Matrix.vecMul_one]
  rfl

/-- The column scalar orbit becomes the literal row scalar line from the
published projective configuration. -/
theorem referenceColumnToRow_scalarOrbit (v : Space) :
    referenceColumnToRow '' referenceScalarOrbit v = scalarLine (referenceColumnToRow v) := by
  simp only [referenceScalarOrbit, Set.image_insert_eq, Set.image_singleton,
    columnToRow_scalar, columnToRow_scalar_sq, scalarLine]

/-- The source's binary vector 1327 is row representative 2045, with index 228. -/
theorem referenceColumnToRow_referenceVector :
    referenceColumnToRow referenceVector = projectiveVector 228 := by decide +kernel

/-- The endpoint pair singled out by column vector 1327. -/
def referencePair : Finset (Fin 22) := {11, 19}

theorem referencePair_card : referencePair.card = 2 := by decide +kernel

/-- The published endpoint pair for this row is {11,19}. -/
theorem referenceVector_endpoints :
    CoreProjectiveAction.endpointPair 228 = referencePair := by decide +kernel

/-- Actual consumer: the binary image comparison reduces to fixation of the
marked row scalar line, with the correct inverse right-row convention. -/
theorem reference_projective_comparison (g : Model) :
    action g referenceVector ∈ referenceScalarOrbit referenceVector ↔
      Matrix.vecMul (projectiveVector 228) ((g.val⁻¹ : Matrix12ˣ) : Matrix12) ∈
        scalarLine (projectiveVector 228) := by
  rw [← referenceColumnToRow_referenceVector, ← referenceColumnToRow_scalarOrbit,
    ← referenceColumnToRow_action]
  constructor
  · exact Set.mem_image_of_mem _
  · rintro ⟨w, hw, he⟩
    exact referenceColumnToRow_injective he ▸ hw

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
