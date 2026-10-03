module
public import Stellmacher.SectionFiveToSeven.SixFourBarredAction
public import Stellmacher.QuotientModuleOffenderFixedPoints
public import Stellmacher.SectionOne.ModuleEquivOffenders

/-!
# Comparing Section Six and witness offender fixed subgroups

For the actual Hypothesis Two data, let V equal sectionSixV S P1 and
let w be any faithful quotient-module witness for P1/C_P1(V) acting on
that original ambient subgroup. Then w.oneJFixedPoints S equals V
intersected with the centralizer of the full canonical barred critical
preimage used in (6.4).

The native Section Two module maps injectively onto V. Conjugating its
canonical quotient action through this multiplicative equivalence gives
a canonical witness acting on the actual V, with its exact centralizer
kernel and conjugation equation. Witness independence identifies w's
fixed subgroup with that of this canonical witness. Equivariant module
transport preserves fixed-subgroup cardinalities and identifies the two
action-defined offender joins. The full canonical preimage maps onto
that join, so the witness fixed-point image theorem gives the displayed
ambient centralizer intersection.

This provides the presentation comparison between Stellmacher (6.4),
journal pp.31–32, and its application in (8.4), p.38. It compares the
action-defined barred joins only; no raw ambient offender equality or
extra normality assertion is used. Source: refs/files/stellmacher-n-group.pdf
and the canonical Section Six notation in SixFourBarredAction.
-/

namespace Stellmacher.SectionsFiveToSeven
open Stellmacher.Later
universe u

public theorem sectionSix_witness_fixed_eq
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (V : Subgroup H) (hV : V = sectionSixV S P1)
    (witness : QuotientModuleWitness P1
      (P1 ⊓ Subgroup.centralizer (V : Set H)) V) :
    witness.oneJFixedPoints S = V ⊓
      Subgroup.centralizer (sectionSixBarredCriticalPreimage h : Set H) := by
  subst V
  let V := sectionSixV S P1
  let Vn := sectionSixLocalV h
  let q := sectionSixQuotientMap h
  let _ := sectionSixQuotientAction h
  let e : Vn ≃* V :=
    (Vn.equivMapOfInjective P1.subtype P1.subtype_injective).trans
      (MulEquiv.subgroupCongr (sectionSix_barred_action_setup h).localV_image)
  have he (v : Vn) : ((e v : V) : H) = ((v : P1) : H) := by
    simp only [e,MulEquiv.trans_apply,MulEquiv.subgroupCongr_apply]
    exact Subgroup.coe_equivMapOfInjective_apply Vn P1.subtype P1.subtype_injective v
  let act : SectionSixBarP1 h →* MulAut V := {
    toFun := fun a => e.symm.trans ((MulDistribMulAction.toMulAut (SectionSixBarP1 h) Vn) a) |>.trans e
    map_one' := by ext v; simp
    map_mul' := by intros a b; ext v; simp [mul_smul] }
  have hact (a : P1) (v : V) : ((act (q a)) v : H) = (a : H) * v * (a : H)⁻¹ := by
    change ((e (q a • e.symm v) : V) : H) = _
    rw [he,SectionTwo.quotientConjugationAction_smul_coe (sectionSixSylow h) q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) a (e.symm v)]
    have hev : (((e.symm v : Vn) : P1) : H) = (v : H) := by
      rw [← he,e.apply_symm_apply]
    change (a : H) * (((e.symm v : Vn) : P1) : H) * (a : H)⁻¹ = _
    rw [hev]
  have hker : q.ker = (P1 ⊓ Subgroup.centralizer (V : Set H)).subgroupOf P1 := by
    rw [show q.ker = sectionSixLocalC h from QuotientGroup.ker_mk' _]
    ext a
    change a ∈ Subgroup.centralizer (Vn : Set P1) ↔ _
    simp only [Subgroup.mem_centralizer_iff,Subgroup.mem_subgroupOf,Subgroup.mem_inf]
    constructor
    · intro ha
      refine ⟨a.property,?_⟩
      intro v hv
      obtain ⟨vn,hvn,hveq⟩ := Subgroup.mem_map.mp
        ((sectionSix_barred_action_setup h).localV_image.ge hv)
      rw [← hveq]
      exact congrArg P1.subtype (ha vn hvn)
    · rintro ⟨_,ha⟩ vn hvn
      apply P1.subtype_injective
      exact ha vn ((sectionSix_barred_action_setup h).localV_image.le
        (Subgroup.mem_map_of_mem P1.subtype hvn))
  let canonical : QuotientModuleWitness P1 (P1 ⊓ Subgroup.centralizer (V : Set H)) V := {
    X := SectionSixBarP1 h
    projection := q
    surjective := QuotientGroup.mk'_surjective _
    kernel_eq := hker
    module_le := by
      change sectionSixV S P1 ≤ P1
      rw [← (sectionSix_barred_action_setup h).localV_image]
      exact Subgroup.map_subtype_le Vn
    action := act
    action_compatible := hact }
  rw [witness.oneJ_fixedPoints_eq canonical S]
  let _ := MulDistribMulAction.compHom V act
  have hequiv : ∀ (a : SectionSixBarP1 h) (v : Vn), e (a • v) = a • e v := by
    intro a v
    change e (a • v) = e (a • e.symm (e v))
    rw [e.symm_apply_apply]
  have hSsub : S.subgroupOf P1 = (sectionSixSylow h : Subgroup P1) := by
    calc
      S.subgroupOf P1 = (((sectionSixSylow h : Subgroup P1).map P1.subtype).subgroupOf P1) :=
        congrArg (fun T : Subgroup H => T.subgroupOf P1) (sectionSix_barred_action_setup h).sylow_image.symm
      _ = _ := subgroupOf_map_subtype_eq _
  have hJ : SectionOne.oneJ (V := V) ((S.subgroupOf P1).map q) =
      sectionSixBarredCritical h := by
    rw [hSsub,← SectionOne.oneJ_eq_of_module_equiv e hequiv]
    rfl
  let Y := sectionSixBarredCriticalPreimage h
  have hYP : Y ≤ P1 := Subgroup.map_subtype_le _
  have hY : (Y.subgroupOf P1).map q = sectionSixBarredCritical h := by
    change ((((sectionSixBarredCritical h).comap q).map P1.subtype).subgroupOf P1).map q = _
    rw [subgroupOf_map_subtype_eq,Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hf := canonical.fixedPoints_map_subtype Y hYP
  dsimp only at hf
  change (FixedPoints.subgroup ((Y.subgroupOf P1).map q) V).map V.subtype = _ at hf
  rw [hY,← hJ] at hf
  exact hf
end Stellmacher.SectionsFiveToSeven
