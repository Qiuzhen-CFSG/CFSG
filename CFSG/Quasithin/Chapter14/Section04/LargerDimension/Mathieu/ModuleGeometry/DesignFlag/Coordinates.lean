module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.SylowOrbit
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativePointCentralizer.Reference.OuterProjective
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.DesignProjection

/-!
# The design hexad of the native six-space

The invariant Gram pairing identifies the native six-space with a row space.
Among the 231 published projective pair-points, precisely the fifteen pairs
inside `{2,7,9,11,19,20}` belong to this space. A left inverse turns this
incidence assertion into small, kernel-checked binary matrix identities.
These are the coordinates for the design/module flag comparison in
Aschbacher--Smith 14.4.12, printed pp.1011--1012 and H.12.1, pp.393--394.
The matrices and projective labels come from the imported ATLAS model.
-/

@[expose] public section
noncomputable section
open Matrix Subgroup Sporadic.Mathieu M22TripleCover
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open CoreProjectiveAction
open Representation.BinaryOffender
open scoped Matrix Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.DesignFlag
open OrbitCertificates
open ActorCatalogue.Native
open ActorCatalogue.NativeParabolics

def markedHexad : Finset (Fin 22) := {2, 7, 9, 11, 19, 20}

def rowFrame : Matrix (Fin 12) (Fin 6) (ZMod 2) := fun i j =>
  if (![51,48,23,1,5,25,45,3,29,5,17,50] i : ℕ).testBit j.val then 1 else 0

def rowDecoder : Matrix (Fin 6) (Fin 12) (ZMod 2) := fun i j =>
  if (![8,11,24,55,31,29] i : ℕ).testBit j.val then 1 else 0

theorem row_decode : rowDecoder * rowFrame = 1 := by decide +kernel

def rowSpace : Submodule (ZMod 2) BinarySpace := rowFrame.mulVecLin.range

theorem mem_rowSpace_iff (v : BinarySpace) :
    v ∈ rowSpace ↔ rowFrame *ᵥ (rowDecoder *ᵥ v) = v := by
  constructor
  · rintro ⟨u, rfl⟩
    change rowFrame *ᵥ (rowDecoder *ᵥ (rowFrame *ᵥ u)) = rowFrame *ᵥ u
    rw [mulVec_mulVec u rowDecoder rowFrame, row_decode, one_mulVec]
  · intro h
    exact ⟨rowDecoder *ᵥ v, h⟩

theorem rowFrame_gram : rowFrame = referenceGram.transpose * orbitMatrix := by decide +kernel

theorem rowSpace_eq_map : rowSpace = parabolicSpace.map referenceColumnToRow := by
  rw [← orbit_range_eq]
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨orbitEmbedding u, ⟨u, rfl⟩, ?_⟩
    change Matrix.vecMul (orbitMatrix *ᵥ u) referenceGram = rowFrame *ᵥ u
    rw [← Matrix.mulVec_transpose, rowFrame_gram, mulVec_mulVec]
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    refine ⟨u, ?_⟩
    change rowFrame *ᵥ u = Matrix.vecMul (orbitMatrix *ᵥ u) referenceGram
    rw [← Matrix.mulVec_transpose, rowFrame_gram, mulVec_mulVec]

def rowProjection : Matrix12 := fromRows ![1,2,4,8,16,32,58,3,56,16,23,9]

theorem rowProjection_eq : rowProjection = rowFrame * rowDecoder := by decide +kernel

theorem rowJ_stable_certificate :
    rowProjection * (matrixJ.transpose * rowFrame) = matrixJ.transpose * rowFrame := by
  decide +kernel

theorem rowSpace_vecMul_J {v : BinarySpace} (hv : v ∈ rowSpace) :
    Matrix.vecMul v matrixJ ∈ rowSpace := by
  obtain ⟨u, rfl⟩ := hv
  rw [mem_rowSpace_iff, mulVec_mulVec, ← rowProjection_eq, ← Matrix.mulVec_transpose]
  change rowProjection *ᵥ (matrixJ.transpose *ᵥ (rowFrame *ᵥ u)) =
    matrixJ.transpose *ᵥ (rowFrame *ᵥ u)
  rw [mulVec_mulVec u matrixJ.transpose rowFrame, mulVec_mulVec, rowJ_stable_certificate]

private theorem incidence_certificate : ∀ i : Fin 231,
    rowProjection *ᵥ projectiveVector i = projectiveVector i ↔
      endpointPair i ⊆ markedHexad := by decide +kernel

theorem representative_mem_iff (i : Fin 231) :
    projectiveVector i ∈ rowSpace ↔ endpointPair i ⊆ markedHexad := by
  rw [mem_rowSpace_iff, mulVec_mulVec, ← rowProjection_eq]
  exact incidence_certificate i

theorem scalarLine_mem_iff (i : Fin 231) {w : BinarySpace}
    (hw : w ∈ scalarLine (projectiveVector i)) :
    w ∈ rowSpace ↔ endpointPair i ⊆ markedHexad := by
  have hclosed (v : BinarySpace) (hv : v ∈ rowSpace) : scalarLine v ⊆ rowSpace := by
    rintro _ (rfl | rfl | rfl)
    · exact hv
    · exact rowSpace_vecMul_J hv
    · exact rowSpace.add_mem hv (rowSpace_vecMul_J hv)
  rw [← representative_mem_iff]
  constructor
  · intro hwspace
    apply hclosed w hwspace
    rw [scalarLine_of_mem hw]
    exact Or.inl rfl
  · exact fun hv => hclosed _ hv hw

def edgePair : Fin 6 → Fin 231 := ![90, 135, 98, 162, 128, 56]

theorem edgePair_mem_rowSpace : ∀ j : Fin 6,
    projectiveVector (edgePair j) ∈ rowSpace := by
  intro j
  rw [mem_rowSpace_iff]
  fin_cases j <;> decide +kernel

theorem edgePair_endpoints : ∀ j : Fin 6, endpointPair (edgePair j) ⊆ markedHexad := by
  decide +kernel

theorem edgePair_covers : ∀ a ∈ markedHexad, ∃ j : Fin 6,
    a ∈ endpointPair (edgePair j) := by decide +kernel

def columnPair : Fin 6 → Fin 231 := ![228,228,128,56,34,98]

theorem columnPair_rowSpace : ∀ j : Fin 6,
    projectiveVector (columnPair j) ∈ rowSpace := by
  intro j
  rw [mem_rowSpace_iff]
  fin_cases j <;> decide +kernel

theorem columnPair_subset : ∀ j : Fin 6, endpointPair (columnPair j) ⊆ markedHexad := by
  decide +kernel

theorem orbitColumns_scalarLine : ∀ j : Fin 6,
    referenceColumnToRow (orbitColumns j) ∈ scalarLine (projectiveVector (columnPair j)) := by
  simp only [scalarLine, Set.mem_insert_iff, Set.mem_singleton_iff]
  decide +kernel

theorem referenceProjection_eq_designProjection : referenceProjection = designProjection := rfl

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.DesignFlag
