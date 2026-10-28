module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.HSWitnesses.Inputs

/-!
# Transport between the ambient HS configuration and its intrinsic action

Perfectness makes the action on a central quotient faithful. The quotient
model therefore preserves the order of the actual actors and fixes the
actual projected copy of L pointwise. Separately, the embedded layer of an
ambient centralizer is identified with the layer of the intrinsic fixed
subgroup by component transport under an isomorphism.

These transports do not identify a cover centralizer with its quotient.
Source application: Aschbacher–Smith 16.3.5, printed p.1179 / PDF p.1196.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G]

private theorem map_layer_le_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (componentLayer A).map e.toMonoidHom ≤ componentLayer B := by
  apply map_le_iff_le_comap.mpr
  exact sSup_le fun K hK => map_le_iff_le_comap.mp (le_sSup (hK.map_equiv e))

private theorem map_layer_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (componentLayer A).map e.toMonoidHom = componentLayer B := by
  apply le_antisymm (map_layer_le_equiv e)
  have h := map_mono (f := e.toMonoidHom) (map_layer_le_equiv e.symm)
  simpa [map_map] using h

/-- The literal ambient layer is the layer of the intrinsic fixed subgroup.
This uses an isomorphism of groups, without a quotient or a cover assumption. -/
noncomputable def centralizerLayerEquiv (E I : Subgroup G)
    (hn : E ≤ normalizer (I : Set G)) (a : E) :
    ComponentTransfer.layerIn (I ⊓ involutionCentralizer (a : G)) ≃*
      componentLayer (inducedAction E I hn a).fixedSubgroup := by
  let C := I ⊓ involutionCentralizer (a : G)
  let f : C ≃* (inducedAction E I hn a).fixedSubgroup :=
    ComponentTransfer.Intrinsic.centralizerEquivFixed (hn a.property)
  exact ((componentLayer C).equivMapOfInjective C.subtype Subtype.val_injective).symm.trans
    ((f.subgroupMap (componentLayer C)).trans (MulEquiv.subgroupCongr (map_layer_equiv f)))

/-- The model action commutes with the actual quotient projection. -/
theorem modelAction_projection (I : Subgroup G)
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier)
    (r : MulAut I) (x : I) :
    modelAction I e r (modelProjection I e x) = modelProjection I e (r x) := by
  change e ((pCore 2 I).quotientAut r (e.symm (e _))) = _
  rw [e.symm_apply_apply, quotientAut_apply_mk]
  rfl

/-- The quotient-model action is faithful whenever the kernel is central
and I is perfect; equality of the two-core with the center is unnecessary. -/
theorem modelAction_injective (I : Subgroup G) [Group.IsPerfect I]
    (hz : pCore 2 I ≤ center I)
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier) :
    Function.Injective (modelAction I e) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro r hr
  apply MulAut.eq_one_of_central_displacement r
  intro x
  apply hz
  have he := congrArg (fun a : MulAut Sporadic.LeechRelated.HS.Carrier =>
    a (modelProjection I e x)) hr
  rw [modelAction_projection] at he
  have hq : QuotientGroup.mk' (pCore 2 I) (r x) = QuotientGroup.mk' (pCore 2 I) x :=
    e.injective he
  exact QuotientGroup.eq.mp hq.symm

/-- Faithfulness survives projection to the actual HS model. -/
theorem quotientAction_injective (E I : Subgroup G) [Group.IsPerfect I]
    (hz : pCore 2 I ≤ center I) (hn : E ≤ normalizer (I : Set G))
    (hf : Function.Injective (inducedAction E I hn))
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier) :
    Function.Injective (quotientAction E I hn e) :=
  (modelAction_injective I hz e).comp hf

/-- Every element of L has a fixed image under every element of E. -/
theorem quotientAction_fixes_component {E L I : Subgroup G}
    (hLI : L ≤ I) (hn : E ≤ normalizer (I : Set G))
    (hc : E ≤ centralizer (L : Set G))
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier)
    (a : E) (l : L) :
    quotientAction E I hn e a (modelProjection I e (Subgroup.inclusion hLI l)) =
      modelProjection I e (Subgroup.inclusion hLI l) := by
  change modelAction I e (inducedAction E I hn a) _ = _
  rw [modelAction_projection]
  congr 1
  apply Subtype.ext
  change (a : G) * (l : G) * (a : G)⁻¹ = l
  rw [← mem_centralizer_iff.mp (hc a.property) l l.property]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

/-- The center/core equality comes from the ambient even-type hypothesis,
not from any unproved simplicity theorem for the concrete HS carrier. -/
theorem Configuration.center_eq_core [Finite G] {𝒦 : GroupClass.{u}}
    {E L I : Subgroup G} {a i : G} (h : Configuration 𝒦 E L I a i) :
    center I = pCore 2 I :=
  h.source.evenType.component_center_eq_twoCore h.setup.involution_i h.component

/-- The actual ambient hypotheses supply the faithful quotient action. -/
theorem Configuration.quotient_faithful [Finite G] {𝒦 : GroupClass.{u}}
    {E L I : Subgroup G} {a i : G} (h : Configuration 𝒦 E L I a i)
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier) :
    Function.Injective (quotientAction E I h.normalizes e) := by
  let := h.component.quasisimple
  exact quotientAction_injective E I h.center_eq_core.ge h.normalizes h.faithful e

/-- Simplicity of the model is inherited from the actual quasisimple component. -/
theorem Configuration.model_simple [Finite G] {𝒦 : GroupClass.{u}}
    {E L I : Subgroup G} {a i : G} (h : Configuration 𝒦 E L I a i)
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier) :
    IsSimpleGroup Sporadic.LeechRelated.HS.Carrier := by
  let := h.component.quasisimple
  let : IsSimpleGroup (I ⧸ center I) := IsQuasisimple.simple
  exact (MulEquiv.isSimpleGroup_congr
    ((QuotientGroup.quotientMulEquivOfEq h.center_eq_core).trans e)).mp inferInstance

/-- Perfectness of the model is inherited through the genuine surjective projection. -/
theorem Configuration.model_perfect [Finite G] {𝒦 : GroupClass.{u}}
    {E L I : Subgroup G} {a i : G} (h : Configuration 𝒦 E L I a i)
    (e : (I ⧸ pCore 2 I) ≃* Sporadic.LeechRelated.HS.Carrier) :
    Group.IsPerfect Sporadic.LeechRelated.HS.Carrier := by
  let := h.component.quasisimple
  exact Group.IsPerfect.ofSurjective (f := modelProjection I e)
    (e.surjective.comp (QuotientGroup.mk'_surjective _))

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses
