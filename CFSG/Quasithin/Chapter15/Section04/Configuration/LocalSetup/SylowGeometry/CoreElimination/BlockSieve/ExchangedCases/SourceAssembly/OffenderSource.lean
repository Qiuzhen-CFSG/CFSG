module
public import CFSG.Quasithin.ChapterC.Section02.OffenderSource
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.SingleComponentGeometry
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.SingleComponentInputs

/-!
# Actual core and offender clauses before the C.2.7 classification

The seed-centralizer geometry identifies the local omega action kernel with
O₂(LR). Characteristic-normalizer control restricts to that same local group,
and the selected component remains outside its marked proper subgroup.
B.2.10 and maximum-elementary replacement now construct the FF module and
a best offender inside the literal image of R, together with every core
clause of C.2.7(1). Both exchanged and single-component source applications
supply local radicality themselves.

No C.2.7 classification input is used here. Its later block and parabolic
alternatives remain distinct source obligations.
Source: Aschbacher--Smith C.2.7(1--2), pp.145--146; 15.4.20, p.1164.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
open SL3Geometry.SourceCases
universe u
variable {G : Type u} [Group G] [Finite G]
variable {d : Source.Geometry G} {i j : Bool} {H U K K₁ : Subgroup G} {r : G}

theorem source_component_core_offenders_of_local_radical
    (h : Input d i j H U K) (L : Subgroup H) (κ : GroupClass.{u})
    (hc : ComponentHypotheses κ H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) L)
    (hr : IsPRadical 2 (((sourceRadical d U).subgroupOf H).subgroupOf
      (L ⊔ (sourceRadical d U).subgroupOf H))) :
    CoreConclusion L ((sourceRadical d U).subgroupOf H) ∧
    OffenderConclusion L ((sourceRadical d U).subgroupOf H) := by
  let R := (sourceRadical d U).subgroupOf H
  let M := d.M₁.subgroupOf H
  let D := L ⊔ R
  have hk : starKernel L R = pCore 2 D :=
    (h.local_module_comparison L hc.normalized hr).2.2.2.2
  have hQR : pCore 2 D ≤ R.subgroupOf D :=
    pCore_le_of_pCore_normalizer_le _ hr.isPGroup hr.2.le
  have hcontrol : (R.subgroupOf D).characteristicNormalizerClosure ≤ M.subgroupOf D :=
    characteristicNormalizerClosure_subgroupOf_le le_sup_right hc.characteristic_control
  have hproper : M.subgroupOf D ≠ ⊤ := by
    intro he
    exact hc.outside (le_sup_left.trans (subgroupOf_eq_top.mp he))
  have hVQ : omegaCoreModule D ≤ pCore 2 D := by
    intro z hz
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hoff := ChapterC.offender_of_characteristic_control
    (omegaCoreModule D) (R.subgroupOf D) (M.subgroupOf D) hr.isPGroup hr.1
    hQR hVQ hk hcontrol hproper (starProjection L R)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  refine ⟨?_,hoff⟩
  refine ⟨hk.ge, hk.le.trans le_sup_left, inferInstance, ?_⟩
  change pCore 2 (D ⧸ starKernel L R) = ⊥
  let e := QuotientGroup.quotientMulEquivOfEq hk
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [pCore_map_iso 2 e, Subgroup.map_bot, pCore_quotient_pCore_eq_bot]

theorem source_component_core_offenders
    (h : Input d i j H U K) (s : Selected H U K K₁ r) (κ : GroupClass.{u})
    (hc : ComponentHypotheses κ H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) (K₁.subgroupOf H)) :
    CoreConclusion (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H) ∧
    OffenderConclusion (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H) :=
  source_component_core_offenders_of_local_radical h _ κ hc
    (source_local_radical h s hc.normalized)

theorem source_single_core_offenders {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G) (h : Input d i j H U K)
    (unique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      d.wholeX ⊔ (d.T : Subgroup G) ≤ N → N = d.M₁)
    (hK : (K.subgroupOf H).IsCComponent)
    (hq : IsQuasisimple (Chapter1.XiQuotient K)) :
    CoreConclusion (K.subgroupOf H) ((sourceRadical d U).subgroupOf H) ∧
    OffenderConclusion (K.subgroupOf H) ((sourceRadical d U).subgroupOf H) :=
  source_component_core_offenders_of_local_radical h _ κ
    (single_component_hypotheses hG h unique hK hq) (single_local_radical h)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly

