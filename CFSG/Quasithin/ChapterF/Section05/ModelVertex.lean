module
public import CFSG.Quasithin.ChapterF.Section05.ModelVertexField
public import CFSG.Quasithin.ChapterF.Section05.ModelSystem
public import Theory.SpecificGroups.OmegaSixThree.UnitaryVertex
/-!
# The literal source unitary extension and the model vertex

The source's projective extension is transported entrywise to the explicit
split-form extension over the concrete field of four elements. The marked
exterior comparison then identifies it with the actual standard vertex group
of the F.5 uniqueness system. The source involution sigma maps to the literal
coordinate graph involution; there are no remaining order, simplicity,
recognition, or comparison premises.

Source: Aschbacher–Smith F.5.1(1) and F.5.3(6), printed pp.300–301.
-/

open Theory.SpecificGroups.ClassicalUnitary
open Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo
open OmegaSixThree.VertexComparison
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05
open GreenBook.LieModels

def modelMatrixExtensionToSplit : UnitaryFour.Extension.MatrixExtension 1 (Nat.le_refl 1) →*
    SplitExtension :=
  SemidirectProduct.map modelMatrixEquivSplit.toMonoidHom (MonoidHom.id _) (by
    intro c
    apply MonoidHom.ext
    intro a
    change modelMatrixEquivSplit (UnitaryFourOuter.action _ _ _ c a) =
      UnitaryFourOuter.action _ _ _ c (modelMatrixEquivSplit a)
    rcases UnitaryFourOuter.c2_cases c with rfl | rfl
    · simp
    · rw [UnitaryFourOuter.action_generator, UnitaryFourOuter.action_generator]
      exact modelMatrixEquivSplit_aut a)

def modelMatrixExtensionEquivSplit :
    UnitaryFour.Extension.MatrixExtension 1 (Nat.le_refl 1) ≃* SplitExtension :=
  MulEquiv.ofBijective modelMatrixExtensionToSplit ⟨by
    intro a b h
    exact SemidirectProduct.ext (modelMatrixEquivSplit.injective
      (congrArg SemidirectProduct.left h)) (congrArg (fun x : SplitExtension => x.right) h), by
    intro x
    refine ⟨⟨modelMatrixEquivSplit.symm x.left,x.right⟩, ?_⟩
    apply SemidirectProduct.ext
    · exact modelMatrixEquivSplit.apply_symm_apply x.left
    · rfl⟩

/-- The literal source unitary extension is the actual model vertex. -/
def modelUnitaryExtensionEquivVertex :
    UnitaryFour.Extension.ProjectiveExtension 1 (Nat.le_refl 1) ≃*
      OmegaSixThree.OrthogonalityGraph.modelSystem.vertexGroup :=
  (UnitaryFour.Extension.extensionEquiv 1 (Nat.le_refl 1)).symm.trans
    (modelMatrixExtensionEquivSplit.trans splitExtensionEquivVertex)

/-- The vertex comparison retains the exact source graph involution. -/
theorem modelUnitaryExtensionEquivVertex_sigma :
    (modelUnitaryExtensionEquivVertex
      (UnitaryFour.Extension.sigma 1 (Nat.le_refl 1))).val =
        OmegaSixThree.vertexGraphInvolution := by
  have hs : (UnitaryFour.Extension.extensionEquiv 1 (Nat.le_refl 1)).symm
      (UnitaryFour.Extension.sigma 1 (Nat.le_refl 1)) =
        UnitaryFourOuter.sigma (UnitaryFour.MatrixField 1) (UnitaryFour.fieldConj 1)
          (UnitaryFour.fieldConj_involutive 1 (Nat.le_refl 1)) := by
    apply (UnitaryFour.Extension.extensionEquiv 1 (Nat.le_refl 1)).injective
    rw [MulEquiv.apply_symm_apply]
    exact (UnitaryFour.Extension.extensionProjection_sigma 1 (Nat.le_refl 1)).symm
  change (splitExtensionEquivVertex (modelMatrixExtensionEquivSplit
    ((UnitaryFour.Extension.extensionEquiv 1 (Nat.le_refl 1)).symm
      (UnitaryFour.Extension.sigma 1 (Nat.le_refl 1))))).val = _
  rw [hs]
  have he : modelMatrixExtensionEquivSplit
      (UnitaryFourOuter.sigma (UnitaryFour.MatrixField 1) (UnitaryFour.fieldConj 1)
        (UnitaryFour.fieldConj_involutive 1 (Nat.le_refl 1))) =
      UnitaryFourOuter.sigma SplitMarking.F starRingAut SplitMarking.star_involutive := by
    apply SemidirectProduct.ext
    · exact map_one modelMatrixEquivSplit
    · rfl
  rw [he]
  exact splitExtensionEquivVertex_sigma

end CFSG.Quasithin.ChapterF.Section05
