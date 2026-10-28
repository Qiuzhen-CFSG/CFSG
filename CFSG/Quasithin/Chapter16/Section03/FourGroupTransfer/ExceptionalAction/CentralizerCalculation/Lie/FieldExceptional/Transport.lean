module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Lie.Basic
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Quotient
public import Theory.GroupAction.PerfectCentralQuotient.ComponentImage
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# The embedded component in an exceptional field model

The faithful central-quotient action retains the distinguished involution's
order. The actual image of L is a component of its full fixed subgroup,
even though fixed points need not all lift to fixed points on the cover.
Restricting the covering to L gives an isomorphism between the image's
central quotient and L/O₂(L). Neither this isomorphism nor the abstract
model pair identifies the image with a standard subfield subgroup.

These are the transport steps for the exceptional field rows of
Aschbacher–Smith 16.1.7(3a) and the calculation in 16.3.5, printed
pp.1172–1173 and 1178–1179 of the 1 March 2004 manuscript.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.FieldExceptional
open Subgroup Theory.GroupTheory PerfectCentralCovering
universe u v
variable {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}
variable {E L I : Subgroup G} {t i : G} {S : Type v} [Group S]

private noncomputable def centerEquiv (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* S) :
    (I ⧸ center I) ≃* S :=
  (QuotientGroup.quotientMulEquivOfEq
    (hG.evenType.component_center_eq_twoCore h.setup.involution_i h.component)).trans e

/-- The actual projected component, retaining its embedding in the model. -/
@[expose] def modelComponent (h : PairContext E L I t i) (hG : Hypothesis1611 𝒦 G)
    (e : (I ⧸ pCore 2 I) ≃* S) : Subgroup S :=
  (L.subgroupOf I).map (h.coreCover hG e).toMonoidHom

/-- The actual automorphism descended through the specified covering. -/
noncomputable def modelInvolution (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* S) : MulAut S :=
  (h.coreCover hG e).autMap (h.coreCover_kernel hG e) h.involutionAction

theorem modelInvolution_orderOf (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* S) :
    orderOf (modelInvolution h hG e) = 2 := by
  rw [modelInvolution, orderOf_injective _ ((h.coreCover hG e).autMap_injective
    (h.coreCover_kernel hG e)), h.involutionAction_orderOf]

private theorem modelInvolution_eq (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* S) :
    modelInvolution h hG e =
      MulAut.centralQuotientAction (centerEquiv h hG e) h.involutionAction := by
  ext x
  obtain ⟨y, rfl⟩ := (h.coreCover hG e).surjective x
  change (h.coreCover hG e).autMap (h.coreCover_kernel hG e)
    h.involutionAction ((h.coreCover hG e).toMonoidHom y) =
    MulAut.centralQuotientAction (centerEquiv h hG e) h.involutionAction
      ((centerEquiv h hG e) (QuotientGroup.mk' (center I) y))
  rw [Cover.autMap_apply, MulAut.centralQuotientAction_apply]
  rfl

private theorem fixed_map {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (a : MulAut A) :
    a.fixedSubgroup.map e.toMonoidHom = (MulAut.congr e a).fixedSubgroup := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [mem_map_equiv, MulAut.mem_fixedSubgroup, MulAut.mem_fixedSubgroup]
  change a (e.symm (e x)) = e.symm (e x) ↔ e (a (e.symm (e x))) = e x
  simp only [e.symm_apply_apply, e.injective.eq_iff]

/-- Component membership is in the full fixed subgroup downstairs. -/
theorem modelComponent_isComponentIn (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* S) :
    IsComponentIn (modelComponent h hG e) (modelInvolution h hG e).fixedSubgroup := by
  have hc := (h.involutionAction.component_image_in_quotient_fixed
    (L.subgroupOf I) h.component_in_action_fixed).map (centerEquiv h hG e)
  rw [fixed_map, map_map] at hc
  rw [modelInvolution_eq]
  exact hc

private noncomputable def componentCover (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* S) :
    Cover L (modelComponent h hG e) where
  toMonoidHom := ((h.coreCover hG e).toMonoidHom.subgroupMap (L.subgroupOf I)).comp
    (subgroupOfEquivOfLe h.proper.le).symm.toMonoidHom
  surjective := ((h.coreCover hG e).toMonoidHom.subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe h.proper.le).symm.surjective
  isPerfect := h.setup.component.quasisimple.toIsPerfect
  ker_le_center := by
    intro x hx
    have hx' : (⟨(x : G), h.proper.le x.property⟩ : I) ∈
        (h.coreCover hG e).toMonoidHom.ker := by
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hz := (h.coreCover hG e).ker_le_center hx'
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact congrArg (fun z : I => (z : G))
      (mem_center_iff.mp hz ⟨(y : G), h.proper.le y.property⟩)

/-- The image's central quotient is the source's smaller two-core quotient.
This does not assert that Z(L) is contained in Z(I). -/
noncomputable def componentCentralQuotientEquiv (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* S) :
    (modelComponent h hG e ⧸ center (modelComponent h hG e)) ≃* (L ⧸ pCore 2 L) :=
  (componentCover h hG e).quotientCenterEquiv.symm.trans
    (QuotientGroup.quotientMulEquivOfEq
      (hG.evenType.component_center_eq_twoCore h.setup.involution_t h.setup.component))

/-- The source supplies simplicity of the ambient model through the actual quotient. -/
theorem model_isSimpleGroup (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* S) : IsSimpleGroup S := by
  let := h.component.quasisimple
  let : IsSimpleGroup (I ⧸ center I) := IsQuasisimple.simple
  exact (centerEquiv h hG e).symm.isSimpleGroup

/-- Perfectness is also inherited; model order and simplicity computations are unnecessary. -/
theorem model_isPerfect (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* S) : Group.IsPerfect S := by
  let := h.component.quasisimple
  exact Group.IsPerfect.ofSurjective (h.coreCover hG e).surjective

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.FieldExceptional
