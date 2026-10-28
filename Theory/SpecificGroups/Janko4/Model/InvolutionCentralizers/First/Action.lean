module

public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.Core
public import Mathlib.GroupTheory.GroupExtension.Defs

/-!
# The full first-centralizer quotient as its concrete matrix action group

The certified coordinates on Q/Z(Q), with Q = O₂(C), give the actual
conjugation homomorphism C → GL₁₂(2). Extraspecial commutator duality and the
self-centralizing two-core identify its kernel with Q. The proved generator
identities identify its full image with TwoCoreLinearModel.actionGroup.
The first isomorphism theorem therefore identifies C/Q with that literal
matrix group, retaining both the quotient map and the embedding of Q in C.

This is the action-group part of the first row in Aschbacher–Smith 16.1.5(9),
printed p.1172, and GLS3 Table 5.3i. The exact sequence below does not assert
a splitting. Identifying the matrix group as the full 3.M₂₂.2 extension,
including its central order-three kernel, is a separate step.
-/

public section

namespace Janko4.InvolutionCentralizers.First

open scoped Matrix
open Subgroup
open OuterReduction.FixedGenerator.NormalizerSquares
open TwoCoreComparison

private noncomputable def coreQuotientCongr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) : (G ⧸ pCore 2 G) ≃* (H ⧸ pCore 2 H) :=
  QuotientGroup.congr (pCore 2 G) (pCore 2 H) e (pCore_map_iso 2 e)

/-- Certified coordinates and actual generators of the centralizer modulo Q. -/
noncomputable def actionGenerators : ActionGenerators :=
  (nonempty_actionGenerators localTwoCoreCentralizerControl center_card_two).some

/-- The actual conjugation action on Q/Z(Q), in certified binary coordinates. -/
noncomputable def quotientAction : involutionCentralizer →* TwoCoreLinearModel.Matrix12ˣ :=
  localAction actionGenerators.coordinates

/-- Faithfulness after quotienting by the intrinsic two-core. -/
theorem quotientAction_ker : quotientAction.ker = involutionTwoCore := by
  let _ := twoCore_extraspecial
  exact le_antisymm
    (CoordinateGenerators.localAction_ker_le_twoCore localTwoCoreCentralizerControl _)
    (twoCore_le_localAction_ker _)

/-- The full action image is the specified matrix group. -/
theorem quotientAction_range : quotientAction.range = TwoCoreLinearModel.actionGroup := by
  let _ := twoCore_extraspecial
  exact actionGenerators.localAction_range

/-- The full matrix-centralizer quotient, not a central quotient of its derived group. -/
noncomputable def matrixQuotientEquiv :
    (involutionCentralizer ⧸ involutionTwoCore) ≃* TwoCoreLinearModel.actionGroup :=
  (QuotientGroup.quotientMulEquivOfEq quotientAction_ker.symm).trans
    ((QuotientGroup.quotientKerEquivRange quotientAction).trans
      (MulEquiv.subgroupCongr quotientAction_range))

/-- The full quotient of the literal centralizer in J₄ by its intrinsic two-core. -/
noncomputable def quotientEquiv :
    (centralizer ⧸ pCore 2 centralizer) ≃* TwoCoreLinearModel.actionGroup :=
  (@coreQuotientCongr centralizer involutionCentralizer inferInstance inferInstance
    centralizerEquiv).trans matrixQuotientEquiv

/-- The quotient equivalence is induced by the actual conjugation action. -/
theorem matrixQuotientEquiv_mk (c : involutionCentralizer) :
    (matrixQuotientEquiv (QuotientGroup.mk' involutionTwoCore c) :
      TwoCoreLinearModel.Matrix12ˣ) = quotientAction c := by rfl

/-- Compatibility of the intrinsic quotient map with the actual matrix action. -/
theorem quotientEquiv_mk (c : centralizer) :
    (quotientEquiv (QuotientGroup.mk' (pCore 2 centralizer) c) :
      TwoCoreLinearModel.Matrix12ˣ) = quotientAction (centralizerEquiv c) := by rfl

/-- The actual short exact sequence with the literal core inclusion. -/
noncomputable def centralizerExtension :
    GroupExtension (pCore 2 centralizer) centralizer TwoCoreLinearModel.actionGroup where
  inl := (pCore 2 centralizer).subtype
  rightHom := quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 centralizer))
  inl_injective := Subtype.val_injective
  range_inl_eq_ker_rightHom := by
    rw [Subgroup.range_subtype, MonoidHom.ker_comp_of_injective _ _ quotientEquiv.injective,
      QuotientGroup.ker_mk']
  rightHom_surjective := quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)

/-- The extension uses the intrinsic subgroup embedding in C_J₄(a). -/
theorem centralizerExtension_inl (q : pCore 2 centralizer) :
    centralizerExtension.inl q = (q : centralizer) := by rfl

/-- The extension projection is the proved full quotient equivalence after
the canonical quotient map. -/
theorem centralizerExtension_rightHom (c : centralizer) :
    centralizerExtension.rightHom c =
      quotientEquiv (QuotientGroup.mk' (pCore 2 centralizer) c) := by rfl

/-- The matrix action retains its pointwise conjugation interpretation. -/
theorem quotientAction_apply (c : involutionCentralizer) (q : involutionTwoCore) :
    (quotientAction c : TwoCoreLinearModel.Matrix12) *ᵥ
        vector actionGenerators.coordinates q =
      vector actionGenerators.coordinates (involutionTwoCoreAction c q) := by
  change (localAction actionGenerators.coordinates c : TwoCoreLinearModel.Matrix12) *ᵥ _ = _
  rw [CoordinateGenerators.localAction_apply]
  exact matrixAction_mulVec actionGenerators.coordinates (involutionTwoCoreAction c) q

end Janko4.InvolutionCentralizers.First
