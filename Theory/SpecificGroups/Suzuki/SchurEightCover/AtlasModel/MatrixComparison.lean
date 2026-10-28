module

public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.BlockModel
public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.MatrixComparison.NativeEmbedding
public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.MatrixComparison.ActionComparison
public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.MatrixComparison.Generation
public import BenderSuzuki.MatrixGroups.Suzuki

/-!
# Assembly of the marked Suzuki matrix comparison

The checked faithful row-line action identifies the degree-65 block model
with the displayed matrix pair. The checked forward and reverse words,
together with generation of every root and torus over F₈, identify that pair
with the entire native root/torus/Weyl closure. Their composition `equiv`
is an unconditional isomorphism preserving both displayed generators.

The earlier conditional constructors remain available. The separate comparison
of the fourfold model's quotient with the block model, and its application
to `coverOfEquiv`, belong to the parent cover construction.
Source: Aschbacher–Smith I.1.1 and I.1.3(5), printed p.407.
-/

@[expose] public section
namespace BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.MatrixComparison

/-- The matrix subgroup is native Sz(8) once full generation is established. -/
noncomputable def nativeEquivOfSurjective
    (hgen : Function.Surjective nativeEmbedding) : PairModel ≃* SuzukiMatrixGroup 1 :=
  MulEquiv.ofBijective nativeEmbedding ⟨nativeEmbedding_injective, hgen⟩

/-- Compose any block comparison with a surjective native embedding. -/
noncomputable def equivOfComparisons (e : BlockModel.Model ≃* PairModel)
    (hgen : Function.Surjective nativeEmbedding) : BlockModel.Model ≃* SuzukiMatrixGroup 1 :=
  e.trans (nativeEquivOfSurjective hgen)

theorem equivOfComparisons_generatorA (e : BlockModel.Model ≃* PairModel)
    (hgen : Function.Surjective nativeEmbedding)
    (ha : e BlockModel.generatorA = pairA) :
    (equivOfComparisons e hgen BlockModel.generatorA).val = glEquiv matrixA := by
  change (nativeEmbedding (e BlockModel.generatorA)).val = glEquiv matrixA
  rw [ha]
  exact nativeEmbedding_pairA

theorem equivOfComparisons_generatorB (e : BlockModel.Model ≃* PairModel)
    (hgen : Function.Surjective nativeEmbedding)
    (hb : e BlockModel.generatorB = pairB) :
    (equivOfComparisons e hgen BlockModel.generatorB).val = glEquiv matrixB := by
  change (nativeEmbedding (e BlockModel.generatorB)).val = glEquiv matrixB
  rw [hb]
  exact nativeEmbedding_pairB

/-- The degree-65 block model is the literal native Suzuki matrix group Sz(8). -/
noncomputable def equiv : BlockModel.Model ≃* SuzukiMatrixGroup 1 :=
  equivOfComparisons ActionComparison.equiv Generation.nativeEmbedding_surjective

/-- The first block generator maps to its displayed matrix under field transport. -/
theorem equiv_generatorA :
    (equiv BlockModel.generatorA).val = glEquiv matrixA :=
  equivOfComparisons_generatorA ActionComparison.equiv Generation.nativeEmbedding_surjective
    ActionComparison.equiv_generatorA

/-- The second block generator maps to its displayed matrix under field transport. -/
theorem equiv_generatorB :
    (equiv BlockModel.generatorB).val = glEquiv matrixB :=
  equivOfComparisons_generatorB ActionComparison.equiv Generation.nativeEmbedding_surjective
    ActionComparison.equiv_generatorB

end BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.MatrixComparison
