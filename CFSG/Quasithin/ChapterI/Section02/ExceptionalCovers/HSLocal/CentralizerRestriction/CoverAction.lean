module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.CoverStructure

/-!
# The literal A₅ quotient and core orbit of the HS cover residual

The cover residual maps onto the alternating preimage through the specified
central quotient. Composing with its five-point action gives X/O₂(X) ≃ A₅,
with exact kernel and representative formulas. The actual image R* retains
the embedded quaternion-square/cyclic-four central product, and conjugation
by lifts in X realizes the model orbit on its noncentral order-four elements.
The A₅ action on the core's central quotient is the already constructed
factored action, with compatibility under the literal cover map.

Source: Aschbacher–Smith I.2.2(5), printed pp.411–412 / PDF pp.422–423.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction

noncomputable def markedResidualEquiv : modelResidual ≃* centralizerTwoResidual e0 :=
  (modelResidual.equivMapOfInjective (localGroup 0).subtype
    (localGroup 0).subtype_injective).trans
    (MulEquiv.subgroupCongr marked_centralizer_residual_eq.symm)

theorem markedResidualEquiv_apply (x : modelResidual) :
    (markedResidualEquiv x : Carrier) = x.val.val := rfl

variable {K : Type*} [Group K] [Finite K]

/-- Restriction of the given modelMap to the actual cover residual. -/
noncomputable def coverResidualMap
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) : centralizerTwoResidual u →* modelResidual :=
  markedResidualEquiv.symm.toMonoidHom.comp
    ((MulEquiv.subgroupCongr (cover_residual_image_and_perfect e hZ u hu).1).toMonoidHom.comp
      ((modelMap e).subgroupMap (centralizerTwoResidual u)))

theorem coverResidualMap_apply
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) (x : centralizerTwoResidual u) :
    (coverResidualMap e hZ u hu x).val.val = modelMap e x := by
  exact congrArg Subtype.val (markedResidualEquiv.apply_symm_apply _)

theorem coverResidualMap_surjective
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) :
    Function.Surjective (coverResidualMap e hZ u hu) :=
  markedResidualEquiv.symm.surjective.comp
    ((MulEquiv.subgroupCongr (cover_residual_image_and_perfect e hZ u hu).1).surjective.comp
      ((modelMap e).subgroupMap_surjective (centralizerTwoResidual u)))

theorem coverResidualMap_ker
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) :
    (coverResidualMap e hZ u hu).ker = (center K).subgroupOf (centralizerTwoResidual u) := by
  ext x
  change coverResidualMap e hZ u hu x = 1 ↔ (x : K) ∈ center K
  rw [← modelMap_ker]
  change _ ↔ modelMap e x = 1
  constructor
  · intro hx
    have hh := congrArg (fun a : modelResidual => a.val.val) hx
    simpa only [coverResidualMap_apply,coe_one] using hh
  · intro hx
    apply Subtype.ext
    apply Subtype.ext
    simpa only [coverResidualMap_apply,coe_one] using hx

/-- The cover residual's actual five-point action. -/
noncomputable def coverA5Action
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) :
    centralizerTwoResidual u →* alternatingGroup (Fin 5) :=
  modelResidualAction.comp (coverResidualMap e hZ u hu)

theorem coverA5Action_surjective
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) : Function.Surjective (coverA5Action e hZ u hu) :=
  modelResidualAction_surjective.comp (coverResidualMap_surjective e hZ u hu)

theorem coverA5Action_ker
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) :
    (coverA5Action e hZ u hu).ker = pCore 2 (centralizerTwoResidual u) := by
  have hk : IsPGroup 2 (coverResidualMap e hZ u hu).ker := by
    rw [coverResidualMap_ker]
    exact (show IsPGroup 2 (center K) from
      IsPGroup.of_card (n := 1) (by simpa using hZ)).comap_subtype
  rw [coverA5Action,← MonoidHom.comap_ker,modelResidualAction_ker,← modelResidual_pCore_eq]
  exact (coverResidualMap e hZ u hu).comap_pCore_of_ker_isPGroup
    (coverResidualMap_surjective e hZ u hu) hk

/-- The actual X/O₂(X) quotient, without a splitting assertion. -/
noncomputable def coverA5Quotient
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) :
    centralizerTwoResidual u ⧸ pCore 2 (centralizerTwoResidual u) ≃*
      alternatingGroup (Fin 5) :=
  (QuotientGroup.quotientMulEquivOfEq (coverA5Action_ker e hZ u hu).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (coverA5Action e hZ u hu)
      (coverA5Action_surjective e hZ u hu))

theorem coverA5Quotient_mk
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) (x : centralizerTwoResidual u) :
    coverA5Quotient e hZ u hu (QuotientGroup.mk' (pCore 2 (centralizerTwoResidual u)) x) =
      modelResidualAction (coverResidualMap e hZ u hu x) := rfl

/-- The image of the literal cover core is the specified symplectic-type
central product, via the actual inclusion into the model carrier. -/
theorem cover_core_image_shape
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) :
    IsQuaternionSquareCyclicFourProduct ((centralizerCore u).map (modelMap e)) := by
  rw [cover_core_image e hZ u hu]
  exact shape_transport markedCoreEquiv (core_shape_of_card_le core_card_le)

/-- Compatibility of the A₅ action on the model core's central quotient
with the actual cover residual action and quotient. -/
theorem coverA5CoreQuotientAction_compatible
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) (x : centralizerTwoResidual u) (r : core) :
    modelA5CoreQuotientAction
      (coverA5Quotient e hZ u hu (QuotientGroup.mk' (pCore 2 (centralizerTwoResidual u)) x))
      (QuotientGroup.mk' (center core) r) =
      QuotientGroup.mk' (center core) (modelCoreAction (coverResidualMap e hZ u hu x) r) :=
  modelA5CoreQuotientAction_apply (coverResidualMap e hZ u hu x) r

/-- The noncentral order-four orbit is realized by elements of the actual
cover residual, acting on their images through the specified modelMap. -/
theorem cover_residual_orderFour_orbit
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) (r s : core)
    (hr : r ∉ center core) (hs : s ∉ center core)
    (hr4 : orderOf r = 4) (hs4 : orderOf s = 4) :
    ∃ x : centralizerTwoResidual u,
      modelMap e x * r.val.val * (modelMap e x)⁻¹ = s.val.val := by
  obtain ⟨g,hg⟩ := modelResidual_orderFour_transitive r s hr hs hr4 hs4
  obtain ⟨x,hx⟩ := coverResidualMap_surjective e hZ u hu g
  refine ⟨x,?_⟩
  have he := congrArg (fun a : modelResidual => a.val.val) hx
  rw [coverResidualMap_apply] at he
  rw [he]
  exact congrArg (fun a : localGroup 0 => (a : Carrier)) hg

/-- The concrete core identifies with R* through its literal carrier inclusion. -/
noncomputable def coverCoreImageEquiv
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) :
    core ≃* (centralizerCore u).map (modelMap e) :=
  markedCoreEquiv.trans (MulEquiv.subgroupCongr (cover_core_image e hZ u hu).symm)

theorem coverCoreImageEquiv_apply
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) (r : core) :
    (coverCoreImageEquiv e hZ u hu r : Carrier) = r.val.val := rfl

/-- Orbit transitivity stated on the literal image R*, including its actual
center and element orders, and realized by the original cover map. -/
theorem cover_core_image_orderFour_orbit
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0)
    (r s : (centralizerCore u).map (modelMap e))
    (hr : r ∉ center ((centralizerCore u).map (modelMap e)))
    (hs : s ∉ center ((centralizerCore u).map (modelMap e)))
    (hr4 : orderOf r = 4) (hs4 : orderOf s = 4) :
    ∃ x : centralizerTwoResidual u,
      modelMap e x * (r : Carrier) * (modelMap e x)⁻¹ = s := by
  let f := coverCoreImageEquiv e hZ u hu
  have hr' : f.symm r ∉ center core := by
    intro hz
    have hh := mem_map_of_mem f.toMonoidHom hz
    rw [map_center_equiv] at hh
    exact hr (by simpa only [MulEquiv.coe_toMonoidHom,MulEquiv.apply_symm_apply] using hh)
  have hs' : f.symm s ∉ center core := by
    intro hz
    have hh := mem_map_of_mem f.toMonoidHom hz
    rw [map_center_equiv] at hh
    exact hs (by simpa only [MulEquiv.coe_toMonoidHom,MulEquiv.apply_symm_apply] using hh)
  obtain ⟨x,hx⟩ := cover_residual_orderFour_orbit e hZ u hu (f.symm r) (f.symm s)
    hr' hs' ((f.symm.orderOf_eq r).trans hr4) ((f.symm.orderOf_eq s).trans hs4)
  have hrval : (f.symm r).val.val = r.val := congrArg Subtype.val (f.apply_symm_apply r)
  have hsval : (f.symm s).val.val = s.val := congrArg Subtype.val (f.apply_symm_apply s)
  exact ⟨x,by simpa only [hrval,hsval] using hx⟩

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction
