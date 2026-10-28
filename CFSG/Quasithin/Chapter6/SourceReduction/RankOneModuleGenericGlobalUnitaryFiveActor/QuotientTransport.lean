module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveFlagAutomorphisms.QuotientAction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryNativeLift.Actions
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.OuterField

/-!
# Transport of the original U₅ actor to the literal native quotient

Restrict the same reversed comparison to the solvable residual. Its inverse
retains the original underlying element. The native lift's left equation
therefore intertwines the residual action with original conjugation; passing
to the canonical two-core quotients gives the exact commuting square.
The original field-kernel theorem then identifies every outer involution's
native coefficient with Hermitian conjugation, without choosing a new marking.

Source: Aschbacher–Smith F.4.29(2), printed p.289 of refs/quasithin.pdf.
This proves the quotient input to actor representation, not the representation
on the plane radical or the opposite endpoint.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryFiveActor
open ChapterF.GreenBook.UnitaryFive
open ChapterF.UnitaryFiveFlagAutomorphisms
variable {G : Type*} [Group G] [Finite G] (U : Model 4)

/-- Restrict the literal parabolic comparison to its solvable residual. -/
def rightFactorEquiv {P L : Subgroup G} (e : P ≃* U.rightParabolic)
    (hr : (solvableResidual P).map P.subtype = L) : L ≃* U.rightLocalImage :=
  let r := ((solvableResidual P).equivMapOfInjective P.subtype P.subtype_injective).trans
    (MulEquiv.subgroupCongr hr)
  r.symm.trans (e.solvableResidualEquiv.trans U.rightLocalImageEquiv)

private theorem rightFactorEquiv_preimage {P L : Subgroup G} (e : P ≃* U.rightParabolic)
    (hr : (solvableResidual P).map P.subtype = L) (x : L) :
    (e.symm (inclusion (map_subtype_le U.rightLocal) (rightFactorEquiv U e hr x))).val = x.val := by
  let r := ((solvableResidual P).equivMapOfInjective P.subtype P.subtype_injective).trans
    (MulEquiv.subgroupCongr hr)
  obtain ⟨y,rfl⟩ := r.surjective x
  change (e.symm ((e.solvableResidualEquiv (r.symm (r y))).val)).val = _
  rw [r.symm_apply_apply]
  change (e.symm (e y.val)).val = _
  rw [e.symm_apply_apply]
  rfl

@[simp] theorem rightFactorEquiv_symm_val {P L : Subgroup G}
    (e : P ≃* U.rightParabolic) (hr : (solvableResidual P).map P.subtype = L)
    (x : U.rightLocalImage) :
    ((rightFactorEquiv U e hr).symm x).val =
      (e.symm (inclusion (map_subtype_le U.rightLocal) x)).val := by
  obtain ⟨x,rfl⟩ := (rightFactorEquiv U e hr).surjective x
  rw [MulEquiv.symm_apply_apply]
  exact (rightFactorEquiv_preimage U e hr x).symm

variable {U} {L K S : Subgroup G}
    (a : UnitarySource.MarkedMiddleAction L K S U.amalgam.reverse)
    (ell : UnitaryNativeLift.Five.LiftReverse U a)
    (hr : (solvableResidual (ChapterF.Source.parabolic ![L,K] S 0)).map
      (ChapterF.Source.parabolic ![L,K] S 0).subtype = L)

/-- The actual lift on the original residual, before taking any quotient. -/
theorem rightLocalAction_factor
    (t : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G)) (x : L) :
    rightLocalAction U (ell.action t) (rightFactorEquiv U a.comparison.left hr x) =
      rightFactorEquiv U a.comparison.left hr
        (L.normalizerMonoidHom (inclusion inf_le_left t) x) := by
  let e := rightFactorEquiv U a.comparison.left hr
  have he (z : U.rightLocalImage) :
      inclusion (map_subtype_le U.rightLocal) (rightLocalAction U (ell.action t) z) =
        (a.action t).left (inclusion (map_subtype_le U.rightLocal) z) := by
    apply Subtype.ext
    exact (rightLocalAction_val U (ell.action t) z).trans
      (UnitaryNativeLift.Five.leftReverse ell t (inclusion (map_subtype_le U.rightLocal) z))
  apply e.symm.injective
  apply Subtype.ext
  rw [MulEquiv.symm_apply_apply]
  change ((rightFactorEquiv U a.comparison.left hr).symm
    (rightLocalAction U (ell.action t) (e x))).val = _
  rw [rightFactorEquiv_symm_val,he,a.left_conjugation]
  rw [←rightFactorEquiv_symm_val U a.comparison.left hr]
  change t.val * (e.symm (e x)).val * t.val⁻¹ = _
  rw [e.symm_apply_apply]
  rfl

/-- Quotient coordinates induced by this very same residual restriction. -/
def rightFactorQuotientEquiv : (L ⧸ pCore 2 L) ≃* Theory.PSL2.Group U.F :=
  (QuotientGroup.congr _ _ (rightFactorEquiv U a.comparison.left hr)
    (pCore_map_iso 2 (rightFactorEquiv U a.comparison.left hr))).trans
      U.rightLocalImageQuotientEquiv

@[simp] theorem rightFactorQuotientEquiv_mk (x : L) :
    rightFactorQuotientEquiv a hr (QuotientGroup.mk' _ x) =
      U.rightLocalImageQuotientEquiv
        (QuotientGroup.mk' _ (rightFactorEquiv U a.comparison.left hr x)) := rfl

/-- The commuting square uses the original conjugation action and literal
core quotient, with original left equal to native right. -/
theorem rightLinearAction_eq_congr {T : Sylow 2 G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (t : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G)) (ht : t.val ∈ (T : Subgroup G)) :
    rightLinearAction U (ell.action t) = MulAut.congr (rightFactorQuotientEquiv a hr)
      (pCoreJoinAction 2 hTL (inclusion le_sup_right (⟨t.val,ht⟩ : T))) := by
  let e := rightFactorQuotientEquiv a hr
  apply MulEquiv.ext
  intro y
  obtain ⟨y,rfl⟩ := e.surjective y
  induction y using Quotient.inductionOn with | h x =>
    change U.rightLocalImageQuotientEquiv
      (rightQuotientAction U (ell.action t)
        (U.rightLocalImageQuotientEquiv.symm (e (QuotientGroup.mk' _ x)))) =
      e (pCoreJoinAction 2 hTL (inclusion le_sup_right (⟨t.val,ht⟩ : T))
        (e.symm (e (QuotientGroup.mk' _ x))))
    rw [e.symm_apply_apply]
    change U.rightLocalImageQuotientEquiv
      (rightQuotientAction U (ell.action t)
        (U.rightLocalImageQuotientEquiv.symm (U.rightLocalImageQuotientEquiv
          (QuotientGroup.mk' _ (rightFactorEquiv U a.comparison.left hr x))))) = _
    rw [U.rightLocalImageQuotientEquiv.symm_apply_apply,rightQuotientAction_mk,
      rightLocalAction_factor a ell hr,pCoreJoinAction_mk]
    rfl

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryFiveActor

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.UnitaryFiveFlagAutomorphisms UnitaryFiveActor
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
variable (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
include d h hH hp hc

/-- The original outer involution has the required native coefficient, for
the same reversed marked action and its same native lift. -/
theorem Preparation.unitaryFive_lift_rightCoefficient
    (a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L)
      U.amalgam.reverse)
    (ell : UnitaryNativeLift.Five.LiftReverse U a)
    (t : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G))
    (htT : t.val ∈ (T : Subgroup G)) (ht : orderOf t = 2)
    (htS : t.val ∉ sourceS L H) : rightCoefficient U (ell.action t) = U.form.conj := by
  have hr := d.reduced_parabolic_residuals h hH.1.1.2 hp (.unitaryFive U hc) 0
  let e := rightFactorQuotientEquiv a hr
  have ht' : orderOf (⟨t.val,htT⟩ : T) = 2 :=
    (Subgroup.orderOf_coe (⟨t.val,htT⟩ : T)).symm.trans
      ((Subgroup.orderOf_coe t).trans ht)
  have hf := d.unitaryFive_outer_involution_field_coefficient h hH hp U hc
    U.local_field_card e (⟨t.val,htT⟩ : T) ht' htS
  have he : rightCoefficient U (ell.action t) =
      unitaryFiveSylowFieldAction h.sylow_normalizes e (⟨t.val,htT⟩ : T) :=
    congrArg (Theory.PSL2.fieldProjection U.F)
      (rightLinearAction_eq_congr a ell hr h.sylow_normalizes t htT)
  ext x
  exact (congrArg (fun f : U.F ≃+* U.F => f x) he).trans
    ((hf x).trans (U.conjugation x).symm)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
