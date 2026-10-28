module

public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.LocalCore
public import Theory.GroupTheory.ExtraspecialCoreOvergroup
public import Theory.GroupTheory.PCoreFrattiniAction
public import Theory.SpecificGroups.Triality.ArmsParabolicAtTwo

/-!
# Core equality and the original triality centralizer action

The original partner Mc has self-centralizing two-core. That core lies in
O₂(H), whose extraspecial center is the marked central involution and is
central in Mc. The central-quotient comparison therefore proves
O₂(Mc) = O₂(H). It also sharpens the ambient normalizer bound to equality.

Transport of the marked Frattini subgroup identifies the exact kernel of
Mc acting on O₂(Mc)/Z(O₂(Mc)). This is the elementary group of order 256,
and Mc/O₂(Mc) acts faithfully on it. Restricting the same action along the
original inclusion H ≤ Mc has kernel O₂(H) and image PSL₂(8), using the
quotient of the full marked first parabolic.

Source: Aschbacher--Smith 14.2.16 and the opening of 14.2.18, pp.986--987.
The genuine marked amalgam is an explicit earlier input. Normality of the
first endpoint, its possible cubic field extension, and ambient recognition
remain with this source-family owner; none is assumed or asserted here.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
include hG hempty hM hu hmany hcard e hH

theorem source_partner_characteristic_two :
    centralizer (pCore 2 Mc : Set Mc) ≤ pCore 2 Mc := by
  have huH := (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e
    H hH.1.1 hH.1.2).1
  have hHM : H ≤ Mc := (show Mc ∈ maximalTwoLocalOvergroups H from
    huH ▸ Set.mem_singleton Mc).2
  have hMcMem : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  exact Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T)
    ⟨Chapter1.mem_H_of_isTwoLocal hMcMem.1.1, hH.1.1.2.trans hHM⟩)

theorem source_partner_core_eq (r : MarkedTriality T M Mc H) :
    Mc.pCoreIn 2 = H.pCoreIn 2 := by
  have huH := (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e
    H hH.1.1 hH.1.2).1
  have hHM : H ≤ Mc := (show Mc ∈ maximalTwoLocalOvergroups H from
    huH ▸ Set.mem_singleton Mc).2
  have hQMc : H.pCoreIn 2 ≤ Mc := (pCoreIn_le 2 H).trans hHM
  let R := (H.pCoreIn 2).subgroupOf Mc
  let eR : R ≃* H.pCoreIn 2 := subgroupOfEquivOfLe hQMc
  let : IsExtraspecial 2 R := IsExtraspecial.of_mulEquiv eR.symm (firstCore_extraspecial r)
  have hQR : pCore 2 Mc ≤ R := by
    intro q hq
    exact source_partner_core_le hG hempty hM hu hmany hcard e hH ⟨q,hq,rfl⟩
  have hcenter : (center R).map R.subtype ≤ center Mc := by
    rintro _ ⟨x,hx,rfl⟩
    have hxC : ((x : Mc) : G) ∈ firstCoreCenter H :=
      ⟨eR x, (centerCongr eR ⟨x,hx⟩).property, rfl⟩
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    have hy : (y : G) ∈ centralizer (firstCoreCenter H : Set G) := by
      rw [← source_partner_centralizer hG hempty hM hu hmany hcard e hH r]
      exact y.property
    exact (hy _ hxC).symm
  have he := pCore_eq_of_extraspecial_overgroup R hQR hcenter
    (source_partner_characteristic_two hG hempty hM hu hmany hcard e hH)
  have hm := congrArg (Subgroup.map Mc.subtype) he
  rw [map_subgroupOf_eq_of_le hQMc] at hm
  exact hm

theorem source_firstCore_normalizer_eq (r : MarkedTriality T M Mc H) :
    normalizer (H.pCoreIn 2 : Set G) = Mc := by
  apply le_antisymm (source_firstCore_normalizer_le hG hempty hM hu hmany hcard e hH r)
  rw [← source_partner_core_eq hG hempty hM hu hmany hcard e hH r]
  exact Mc.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc))

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic

namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}

omit [Finite G] in
/-- The first core has the literal model Frattini subgroup. -/
theorem firstCore_center_eq_frattini (r : MarkedTriality T M Mc H) :
    center (H.pCoreIn 2) = frattini (H.pCoreIn 2) := by
  let f := firstCoreEquiv r
  apply map_injective (f := f.toMonoidHom) f.injective
  rw [center_map_equiv f, frattini_map_equiv f]
  exact RadicalCoordinates.center_radical_arms_eq_frattini _ rfl

/-- The center quotient used in 14.2.18, before any action is identified. -/
abbrev PartnerCoreModule (Mc : Subgroup G) := pCore 2 Mc ⧸ center (pCore 2 Mc)

/-- Conjugation on the literal core followed by its central quotient. -/
def partnerCoreAction (Mc : Subgroup G) : Mc →* MulAut (PartnerCoreModule Mc) :=
  (quotientAut (center (pCore 2 Mc))).comp (MulAut.conjNormal : Mc →* MulAut (pCore 2 Mc))

variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)

/-- Identify the intrinsic partner core with the already marked embedded core. -/
def sourcePartnerCoreEquiv (r : MarkedTriality T M Mc H) :
    pCore 2 Mc ≃* H.pCoreIn 2 :=
  ((pCore 2 Mc).equivMapOfInjective Mc.subtype Mc.subtype_injective).trans
    (MulEquiv.subgroupCongr (source_partner_core_eq hG hempty hM hu hmany hcard e hH r))

include hG hempty hM hu hmany hcard e hH

theorem source_partner_core_extraspecial (r : MarkedTriality T M Mc H) :
    IsExtraspecial 2 (pCore 2 Mc) :=
  IsExtraspecial.of_mulEquiv (sourcePartnerCoreEquiv hG hempty hM hu hmany hcard e hH r).symm
    (firstCore_extraspecial r)

theorem source_partner_core_card (r : MarkedTriality T M Mc H) :
    Nat.card (pCore 2 Mc) = 512 :=
  (Nat.card_congr (sourcePartnerCoreEquiv hG hempty hM hu hmany hcard e hH r).toEquiv).trans
    (firstCore_card r)

theorem source_partner_core_center_eq_frattini (r : MarkedTriality T M Mc H) :
    center (pCore 2 Mc) = frattini (pCore 2 Mc) := by
  let f := sourcePartnerCoreEquiv hG hempty hM hu hmany hcard e hH r
  apply map_injective (f := f.toMonoidHom) f.injective
  rw [center_map_equiv f, frattini_map_equiv f]
  exact firstCore_center_eq_frattini r

/-- The exact action kernel required at the start of source 14.2.18. -/
theorem source_partner_core_action_kernel (r : MarkedTriality T M Mc H) :
    (partnerCoreAction Mc).ker = pCore 2 Mc := by
  have hk (N : Subgroup (pCore 2 Mc)) [N.Characteristic]
      (hN : N = frattini (pCore 2 Mc)) :
      ((quotientAut N).comp (MulAut.conjNormal : Mc →* MulAut (pCore 2 Mc))).ker =
        pCore 2 Mc := by
    subst N
    exact pCore_frattini_action_kernel 2
      (source_partner_characteristic_two hG hempty hM hu hmany hcard e hH)
  exact hk _ (source_partner_core_center_eq_frattini hG hempty hM hu hmany hcard e hH r)

/-- The source module is the genuine elementary group of order 256. -/
theorem source_partner_core_module (r : MarkedTriality T M Mc H) :
    IsElementaryAbelian 2 (PartnerCoreModule Mc) ∧ Nat.card (PartnerCoreModule Mc) = 256 := by
  let := source_partner_core_extraspecial hG hempty hM hu hmany hcard e hH r
  refine ⟨IsExtraspecial.quotient_elementary_abelian 2 _, ?_⟩
  have hc := card_eq_card_quotient_mul_card_subgroup (center (pCore 2 Mc))
  rw [source_partner_core_card hG hempty hM hu hmany hcard e hH r,
    IsExtraspecial.center_order_p 2 (pCore 2 Mc)] at hc
  change Nat.card (pCore 2 Mc ⧸ center (pCore 2 Mc)) = 256
  omega

/-- The induced action of Mc/O₂(Mc) on the same central quotient. -/
def sourcePartnerQuotientAction (r : MarkedTriality T M Mc H) :
    (Mc ⧸ pCore 2 Mc) →* MulAut (PartnerCoreModule Mc) :=
  QuotientGroup.lift (pCore 2 Mc) (partnerCoreAction Mc)
    (source_partner_core_action_kernel hG hempty hM hu hmany hcard e hH r).ge

theorem sourcePartnerQuotientAction_mk (r : MarkedTriality T M Mc H) (x : Mc) :
    sourcePartnerQuotientAction hG hempty hM hu hmany hcard e hH r
      (QuotientGroup.mk' (pCore 2 Mc) x) = partnerCoreAction Mc x := rfl

/-- Faithfulness on the source module follows from the exact kernel, not a
postulated representation or a replacement quotient. -/
theorem sourcePartnerQuotientAction_injective (r : MarkedTriality T M Mc H) :
    Function.Injective (sourcePartnerQuotientAction hG hempty hM hu hmany hcard e hH r) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 Mc) x
  apply (QuotientGroup.eq_one_iff y).mpr
  rw [← source_partner_core_action_kernel hG hempty hM hu hmany hcard e hH r]
  exact hx

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic

namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}

/-- The quotient of the full first endpoint, with its intrinsic two-core. -/
def firstQuotientEquiv (r : MarkedTriality T M Mc H) :
    (H ⧸ pCore 2 H) ≃* Theory.PSL2.BinaryGroup 3 :=
  (QuotientGroup.congr _ _ r.left (pCore_map_iso 2 r.left)).trans
    (parabolicArmsQuotientEquivPSL2AtTwo (binaryParameters 1 Nat.zero_lt_one)
      rfl (by simp only [binaryParameters_q, pow_one]))

variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
include hG hempty hM hu hmany hcard e hH

theorem source_first_le_partner : H ≤ Mc := by
  have huH := (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e
    H hH.1.1 hH.1.2).1
  exact (show Mc ∈ maximalTwoLocalOvergroups H from huH ▸ Set.mem_singleton Mc).2

/-- The first endpoint acts on the same partner-core quotient by inclusion. -/
def firstCoreAction : H →* MulAut (PartnerCoreModule Mc) :=
  (partnerCoreAction Mc).comp (inclusion
    (source_first_le_partner hG hempty hM hu hmany hcard e hH))

theorem source_first_core_action_kernel (r : MarkedTriality T M Mc H) :
    (firstCoreAction hG hempty hM hu hmany hcard e hH).ker = pCore 2 H := by
  change (partnerCoreAction Mc).ker.comap (inclusion _) = _
  rw [source_partner_core_action_kernel hG hempty hM hu hmany hcard e hH r]
  ext x
  constructor
  · intro hx
    have hx' : (x : G) ∈ Mc.pCoreIn 2 := ⟨inclusion
      (source_first_le_partner hG hempty hM hu hmany hcard e hH) x, hx, rfl⟩
    rw [source_partner_core_eq hG hempty hM hu hmany hcard e hH r] at hx'
    obtain ⟨y,hy,he⟩ := hx'
    exact (Subtype.ext he : y = x) ▸ hy
  · intro hx
    have hx' : (x : G) ∈ H.pCoreIn 2 := ⟨x,hx,rfl⟩
    rw [← source_partner_core_eq hG hempty hM hu hmany hcard e hH r] at hx'
    obtain ⟨y,hy,he⟩ := hx'
    change inclusion (source_first_le_partner hG hempty hM hu hmany hcard e hH) x ∈ pCore 2 Mc
    exact (Subtype.ext he : y = inclusion
      (source_first_le_partner hG hempty hM hu hmany hcard e hH) x) ▸ hy

/-- The first endpoint's actual action image is PSL₂(8). This uses its literal
inclusion in Mc and the same central quotient on which Mc acts. -/
def sourceFirstActionImageEquiv (r : MarkedTriality T M Mc H) :
    (firstCoreAction hG hempty hM hu hmany hcard e hH).range ≃* Theory.PSL2.BinaryGroup 3 :=
  (QuotientGroup.quotientKerEquivRange
    (firstCoreAction hG hempty hM hu hmany hcard e hH)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq
        (source_first_core_action_kernel hG hempty hM hu hmany hcard e hH r)).trans
          (firstQuotientEquiv r))

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
