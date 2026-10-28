module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.CoordinateGenerators.RawAction
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases

/-!
# Irreducibility of the raw max2 column action

For the literal matrices X and Y, put T = XYXYY and S = ∑ i < 11, T^i.
The finite identities below give S(1 + X)S = e₀ ⊗ r, where r is the binary
row with packed value 2736. Both e₀ and r are cyclic: twelve successive
images under X and Y form bases, with explicit inverses certified below.

An invariant subspace containing a nonzero vector therefore contains e₀:
some cyclic row detects the vector, and the rank-one operator extracts e₀.
The cyclic column basis then puts the whole space in that subspace. All
matrix products, row recurrences and inverse identities are checked by the
Lean kernel. This uses only the raw matrices, with no group recognition.

Source motivation: GLS3, Table 5.3i, printed p.270, note 1,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`. The left-column convention and the
ATLAS word provenance are recorded in `CoordinateGenerators.RawAction`.
The elementary binary calculation here supplies the missing irreducibility
for those exact matrices, before any identification with the two-core.
-/

open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreComparison.CoordinateGenerators.Realization.ActionCore
open TwoCoreLinearModel
set_option maxRecDepth 4000

private abbrev Vector12 := Fin 12 → ZMod 2

private def Preserves (U : Submodule (ZMod 2) Vector12) (M : Matrix12) : Prop :=
  ∀ v ∈ U, M *ᵥ v ∈ U

private theorem preserves_one (U : Submodule (ZMod 2) Vector12) : Preserves U 1 := by
  intro v hv
  simpa only [Matrix.one_mulVec] using hv

private theorem preserves_mul {U : Submodule (ZMod 2) Vector12} {A B : Matrix12}
    (ha : Preserves U A) (hb : Preserves U B) : Preserves U (A * B) := by
  intro v hv
  rw [← Matrix.mulVec_mulVec]
  exact ha _ (hb _ hv)

private theorem preserves_add {U : Submodule (ZMod 2) Vector12} {A B : Matrix12}
    (ha : Preserves U A) (hb : Preserves U B) : Preserves U (A + B) := by
  intro v hv
  rw [Matrix.add_mulVec]
  exact U.add_mem (ha _ hv) (hb _ hv)

private def mxy : Matrix12 := fromRows ![34, 516, 560, 545, 928, 352, 2304, 512, 776, 1024, 288, 768]

private theorem step_xy : rawMatrixX * rawMatrixY = mxy := by decide +kernel

private def mxyx : Matrix12 := fromRows ![3090, 1160, 2224, 145, 3792, 1360, 64, 2176, 3268, 1024, 3152, 192]

private theorem step_xyx : mxy * rawMatrixX = mxyx := by decide +kernel

private def mxyxy : Matrix12 := fromRows ![868, 1584, 1728, 1346, 1128, 2920, 8, 1024, 1321, 288, 616, 1800]

private theorem step_xyxy : mxyx * rawMatrixY = mxyxy := by decide +kernel

private def mxyxyy : Matrix12 := fromRows ![2441, 736, 1832, 2604, 952, 2712, 16, 288, 2994, 2176, 920, 2608]

private theorem step_xyxyy : mxyxy * rawMatrixY = mxyxyy := by decide +kernel

private theorem word_preserves {U : Submodule (ZMod 2) Vector12}
    (hx : Preserves U rawMatrixX) (hy : Preserves U rawMatrixY) : Preserves U mxyxyy := by
  have hxy := preserves_mul hx hy
  rw [step_xy] at hxy
  have hxyx := preserves_mul hxy hx
  rw [step_xyx] at hxyx
  have hxyxy := preserves_mul hxyx hy
  rw [step_xyxy] at hxyxy
  have hxyxyy := preserves_mul hxyxy hy
  rwa [step_xyxyy] at hxyxyy

private def powers : Fin 11 → Matrix12 :=
  ![fromRows ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048],
    fromRows ![2441, 736, 1832, 2604, 952, 2712, 16, 288, 2994, 2176, 920, 2608],
    fromRows ![775, 808, 30, 1324, 286, 2564, 952, 298, 994, 2832, 2950, 2960],
    fromRows ![3955, 902, 3164, 4022, 2030, 1432, 286, 2534, 2682, 2746, 3562, 2970],
    fromRows ![2243, 2010, 1796, 1874, 1254, 158, 2030, 4066, 844, 636, 382, 854],
    fromRows ![105, 2798, 1922, 482, 3576, 3452, 1254, 978, 3622, 3252, 3430, 1362],
    fromRows ![2349, 1788, 874, 762, 38, 1582, 3576, 858, 3704, 1664, 3418, 2402],
    fromRows ![3991, 3596, 374, 2140, 3920, 3684, 38, 2134, 564, 2616, 2430, 2538],
    fromRows ![1091, 3116, 1866, 1180, 2354, 3208, 3920, 3152, 1672, 444, 1878, 742],
    fromRows ![2273, 3636, 2166, 3076, 2626, 676, 2354, 2560, 20, 3766, 1738, 1760],
    fromRows ![2065, 3872, 1736, 3712, 64, 1040, 2626, 688, 1168, 3296, 740, 176]]

private theorem powers_zero : powers 0 = 1 := by decide +kernel

private theorem powers_step (i : Fin 10) :
    powers i.succ = powers i.castSucc * mxyxyy := by
  revert i
  decide +kernel

private theorem powers_preserve {U : Submodule (ZMod 2) Vector12}
    (hx : Preserves U rawMatrixX) (hy : Preserves U rawMatrixY) (i : Fin 11) :
    Preserves U (powers i) := by
  refine Fin.induction (motive := fun j => Preserves U (powers j)) ?_ ?_ i
  · rw [powers_zero]
    exact preserves_one U
  · intro j hj
    rw [powers_step]
    exact preserves_mul hj (word_preserves hx hy)

private def average : Matrix12 := fromRows ![3935, 2736, 0, 2736, 0, 2736, 0, 2736, 0, 2736, 2736, 0]

private theorem average_eq : average = ∑ i, powers i := by decide +kernel

private theorem average_preserves {U : Submodule (ZMod 2) Vector12}
    (hx : Preserves U rawMatrixX) (hy : Preserves U rawMatrixY) : Preserves U average := by
  intro v hv
  rw [average_eq, Matrix.sum_mulVec]
  exact U.sum_mem fun i _ => powers_preserve hx hy i v hv

private def projectionMatrix : Matrix12 := fromRows ![2736, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem projection_eq :
    average * (1 + rawMatrixX) * average = projectionMatrix := by decide +kernel

private theorem projection_preserves {U : Submodule (ZMod 2) Vector12}
    (hx : Preserves U rawMatrixX) (hy : Preserves U rawMatrixY) :
    Preserves U projectionMatrix := by
  rw [← projection_eq]
  exact preserves_mul
    (preserves_mul (average_preserves hx hy) (preserves_add (preserves_one U) hx))
    (average_preserves hx hy)

private def columnVectors : Matrix12 := fromRows ![1, 4, 8, 2, 64, 256, 16, 3714, 32, 3440, 2048, 2842]

private def columnVectorsInv : Matrix12 := fromRows ![1, 8, 2, 4, 64, 256, 16, 3988, 32, 3180, 1904, 1024]

private theorem columnVectors_inv : columnVectorsInv * columnVectors = 1 := by decide +kernel

private theorem columnVectors_step1 :
    columnVectors 1 = rawMatrixY *ᵥ columnVectors 0 := by decide +kernel

private theorem columnVectors_step2 :
    columnVectors 2 = rawMatrixX *ᵥ columnVectors 1 := by decide +kernel

private theorem columnVectors_step3 :
    columnVectors 3 = rawMatrixY *ᵥ columnVectors 1 := by decide +kernel

private theorem columnVectors_step4 :
    columnVectors 4 = rawMatrixY *ᵥ columnVectors 2 := by decide +kernel

private theorem columnVectors_step5 :
    columnVectors 5 = rawMatrixX *ᵥ columnVectors 4 := by decide +kernel

private theorem columnVectors_step6 :
    columnVectors 6 = rawMatrixY *ᵥ columnVectors 4 := by decide +kernel

private theorem columnVectors_step7 :
    columnVectors 7 = rawMatrixY *ᵥ columnVectors 5 := by decide +kernel

private theorem columnVectors_step8 :
    columnVectors 8 = rawMatrixX *ᵥ columnVectors 6 := by decide +kernel

private theorem columnVectors_step9 :
    columnVectors 9 = rawMatrixX *ᵥ columnVectors 7 := by decide +kernel

private theorem columnVectors_step10 :
    columnVectors 10 = rawMatrixY *ᵥ columnVectors 7 := by decide +kernel

private theorem columnVectors_step11 :
    columnVectors 11 = rawMatrixY *ᵥ columnVectors 9 := by decide +kernel

private def rowVectors : Matrix12 := fromRows ![2736, 1984, 3368, 3156, 617, 1429, 410, 3683, 614, 3475, 686, 653]

private def rowVectorsInv : Matrix12 := fromRows ![2700, 2140, 2243, 2819, 3362, 3792, 1574, 2085, 1560, 2409, 368, 703]

private theorem rowVectors_inv : rowVectorsInv * rowVectors = 1 := by decide +kernel

private theorem rowVectors_step1 :
    rowVectors 1 = Matrix.vecMul (rowVectors 0) rawMatrixY := by decide +kernel

private theorem rowVectors_step2 :
    rowVectors 2 = Matrix.vecMul (rowVectors 1) rawMatrixY := by decide +kernel

private theorem rowVectors_step3 :
    rowVectors 3 = Matrix.vecMul (rowVectors 2) rawMatrixX := by decide +kernel

private theorem rowVectors_step4 :
    rowVectors 4 = Matrix.vecMul (rowVectors 3) rawMatrixY := by decide +kernel

private theorem rowVectors_step5 :
    rowVectors 5 = Matrix.vecMul (rowVectors 4) rawMatrixX := by decide +kernel

private theorem rowVectors_step6 :
    rowVectors 6 = Matrix.vecMul (rowVectors 4) rawMatrixY := by decide +kernel

private theorem rowVectors_step7 :
    rowVectors 7 = Matrix.vecMul (rowVectors 5) rawMatrixY := by decide +kernel

private theorem rowVectors_step8 :
    rowVectors 8 = Matrix.vecMul (rowVectors 6) rawMatrixX := by decide +kernel

private theorem rowVectors_step9 :
    rowVectors 9 = Matrix.vecMul (rowVectors 7) rawMatrixX := by decide +kernel

private theorem rowVectors_step10 :
    rowVectors 10 = Matrix.vecMul (rowVectors 7) rawMatrixY := by decide +kernel

private theorem rowVectors_step11 :
    rowVectors 11 = Matrix.vecMul (rowVectors 8) rawMatrixY := by decide +kernel

private theorem projection_rank_one :
    projectionMatrix = Matrix.vecMulVec (columnVectors 0) (rowVectors 0) := by decide +kernel

private theorem extraction {U : Submodule (ZMod 2) Vector12}
    (hx : Preserves U rawMatrixX) (hy : Preserves U rawMatrixY) :
    ∀ i : Fin 12, ∀ v ∈ U, (rowVectors i ⬝ᵥ v) • columnVectors 0 ∈ U := by
  have h0 : ∀ v ∈ U, (rowVectors 0 ⬝ᵥ v) • columnVectors 0 ∈ U := by
    intro v hv
    have hp := projection_preserves hx hy v hv
    rw [projection_rank_one, Matrix.vecMulVec_mulVec] at hp
    simpa only [op_smul_eq_smul] using hp
  have h1 : ∀ v ∈ U, (rowVectors 1 ⬝ᵥ v) • columnVectors 0 ∈ U := by
    intro v hv
    rw [rowVectors_step1, ← Matrix.dotProduct_mulVec]
    exact h0 _ (hy _ hv)
  have h2 : ∀ v ∈ U, (rowVectors 2 ⬝ᵥ v) • columnVectors 0 ∈ U := by
    intro v hv
    rw [rowVectors_step2, ← Matrix.dotProduct_mulVec]
    exact h1 _ (hy _ hv)
  have h3 : ∀ v ∈ U, (rowVectors 3 ⬝ᵥ v) • columnVectors 0 ∈ U := by
    intro v hv
    rw [rowVectors_step3, ← Matrix.dotProduct_mulVec]
    exact h2 _ (hx _ hv)
  have h4 : ∀ v ∈ U, (rowVectors 4 ⬝ᵥ v) • columnVectors 0 ∈ U := by
    intro v hv
    rw [rowVectors_step4, ← Matrix.dotProduct_mulVec]
    exact h3 _ (hy _ hv)
  have h5 : ∀ v ∈ U, (rowVectors 5 ⬝ᵥ v) • columnVectors 0 ∈ U := by
    intro v hv
    rw [rowVectors_step5, ← Matrix.dotProduct_mulVec]
    exact h4 _ (hx _ hv)
  have h6 : ∀ v ∈ U, (rowVectors 6 ⬝ᵥ v) • columnVectors 0 ∈ U := by
    intro v hv
    rw [rowVectors_step6, ← Matrix.dotProduct_mulVec]
    exact h4 _ (hy _ hv)
  have h7 : ∀ v ∈ U, (rowVectors 7 ⬝ᵥ v) • columnVectors 0 ∈ U := by
    intro v hv
    rw [rowVectors_step7, ← Matrix.dotProduct_mulVec]
    exact h5 _ (hy _ hv)
  have h8 : ∀ v ∈ U, (rowVectors 8 ⬝ᵥ v) • columnVectors 0 ∈ U := by
    intro v hv
    rw [rowVectors_step8, ← Matrix.dotProduct_mulVec]
    exact h6 _ (hx _ hv)
  have h9 : ∀ v ∈ U, (rowVectors 9 ⬝ᵥ v) • columnVectors 0 ∈ U := by
    intro v hv
    rw [rowVectors_step9, ← Matrix.dotProduct_mulVec]
    exact h7 _ (hx _ hv)
  have h10 : ∀ v ∈ U, (rowVectors 10 ⬝ᵥ v) • columnVectors 0 ∈ U := by
    intro v hv
    rw [rowVectors_step10, ← Matrix.dotProduct_mulVec]
    exact h7 _ (hy _ hv)
  have h11 : ∀ v ∈ U, (rowVectors 11 ⬝ᵥ v) • columnVectors 0 ∈ U := by
    intro v hv
    rw [rowVectors_step11, ← Matrix.dotProduct_mulVec]
    exact h8 _ (hy _ hv)
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11

private theorem columns_mem {U : Submodule (ZMod 2) Vector12}
    (hx : Preserves U rawMatrixX) (hy : Preserves U rawMatrixY)
    (h0 : columnVectors 0 ∈ U) : ∀ i : Fin 12, columnVectors i ∈ U := by
  have h1 : columnVectors 1 ∈ U := by
    rw [columnVectors_step1]
    exact hy _ h0
  have h2 : columnVectors 2 ∈ U := by
    rw [columnVectors_step2]
    exact hx _ h1
  have h3 : columnVectors 3 ∈ U := by
    rw [columnVectors_step3]
    exact hy _ h1
  have h4 : columnVectors 4 ∈ U := by
    rw [columnVectors_step4]
    exact hy _ h2
  have h5 : columnVectors 5 ∈ U := by
    rw [columnVectors_step5]
    exact hx _ h4
  have h6 : columnVectors 6 ∈ U := by
    rw [columnVectors_step6]
    exact hy _ h4
  have h7 : columnVectors 7 ∈ U := by
    rw [columnVectors_step7]
    exact hy _ h5
  have h8 : columnVectors 8 ∈ U := by
    rw [columnVectors_step8]
    exact hx _ h6
  have h9 : columnVectors 9 ∈ U := by
    rw [columnVectors_step9]
    exact hx _ h7
  have h10 : columnVectors 10 ∈ U := by
    rw [columnVectors_step10]
    exact hy _ h7
  have h11 : columnVectors 11 ∈ U := by
    rw [columnVectors_step11]
    exact hy _ h9
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11

/-- The two literal left-column matrices act irreducibly on binary twelve-space. -/
public theorem raw_invariant_submodule (U : Submodule (ZMod 2) (Fin 12 → ZMod 2))
    (hx : ∀ v ∈ U, rawMatrixX *ᵥ v ∈ U)
    (hy : ∀ v ∈ U, rawMatrixY *ᵥ v ∈ U) : U = ⊥ ∨ U = ⊤ := by
  by_cases hu : U = ⊥
  · exact Or.inl hu
  right
  obtain ⟨v, hv, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hu
  have hex : ∃ i : Fin 12, rowVectors i ⬝ᵥ v ≠ 0 := by
    by_contra! h
    have hr : rowVectors *ᵥ v = 0 := funext h
    have he := congrArg (fun w => rowVectorsInv *ᵥ w) hr
    rw [Matrix.mulVec_mulVec, rowVectors_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at he
    exact hn he
  obtain ⟨i, hi⟩ := hex
  have hbinary : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide +kernel
  have hc : columnVectors 0 ∈ U := by
    have hm := extraction hx hy i v hv
    rwa [hbinary _ hi, one_smul] at hm
  apply top_unique
  intro w _
  have hw : columnVectors.transpose *ᵥ (columnVectorsInv.transpose *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, columnVectors_inv, Matrix.transpose_one,
      Matrix.one_mulVec]
  rw [← hw, Matrix.mulVec_eq_sum]
  simp only [op_smul_eq_smul, Matrix.transpose_transpose]
  exact U.sum_mem fun j _ => U.smul_mem _ (columns_mem hx hy hc j)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreComparison.CoordinateGenerators.Realization.ActionCore
