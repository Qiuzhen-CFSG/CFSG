module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness
public import CFSG.Quasithin.Chapter1.Section01
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Ambient
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The original involution hypotheses in an escaping plane overgroup

Apply 1.1.6 to N_G(O₂(I)). The common Sylow theorem puts its Sylow group
at the same S = C_T(ZS). Its intersection core lies in the core of I∩Mc,
so its centralizer bound descends to I. The element marking is literal:
every nonidentity z in Ω₁Z(T) has order two and C_G(z) = Mc.

Source: Aschbacher--Smith, 15.2.20(1), printed p.1113, refs/quasithin.pdf.
-/

public section

open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
open Section01 Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- Every nonidentity element of Z is the actual central involution whose centralizer is Mc. -/
theorem marked_centralizer {I : Subgroup G} (hI : PlaneEscapes Mc ZS I)
    {z : G} (hz : z ∈ centralInvolutions T) (hne : z ≠ 1) :
    orderOf z = 2 ∧ centralizer ({z} : Set G) = Mc := by
  have hc := (d.escape_index hI).1
  have ho : orderOf z = 2 := by
    have hd : orderOf (⟨z,hz⟩ : centralInvolutions T) ∣ 2 :=
      hc ▸ orderOf_dvd_natCard (⟨z,hz⟩ : centralInvolutions T)
    rw [← Subgroup.orderOf_coe] at hd
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left (by simpa using hne)
  refine ⟨ho,?_⟩
  have he : zpowers z = centralInvolutions T := eq_of_le_of_card_ge
    (zpowers_le.mpr hz) (by rw [Nat.card_zpowers,ho,hc])
  rw [d.partner_eq,← he,zpowers_eq_closure,centralizer_closure]

/-- Original 15.2.20(1), with the literal central involution and Sylow subgroup of I. -/
theorem lemma115 {I : Subgroup G} (hI : PlaneEscapes Mc ZS I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = planeSylow T ZS)
    {z : G} (hz : z ∈ centralInvolutions T) (hne : z ≠ 1) :
    Chapter1.Lemma115Hypotheses I P Mc z := by
  have hm := marked_centralizer d hI hz hne
  have hzT := centralInvolutions_le_sylow T hz
  have hzc := centralInvolutions_le_centralizer_sylow T hz
  have hMc : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hsource.partner ▸ Set.mem_singleton Mc).1
  have hTMc : (T : Subgroup G) ≤ Mc := by
    rw [← hm.2]
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (hzc t ht)
  let B := I.pCoreIn 2
  have hBne : B ≠ ⊥ := hI.1
  have hIN : I ≤ normalizer (B : Set G) := by
    simpa only [B,pCoreIn,normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using
      (pCore 2 I).le_normalizer_map I.subtype
  let N := normalizer (B : Set G)
  have hN : PlaneEscapes Mc ZS N :=
    ⟨Chapter1.mem_H_of_isTwoLocal ⟨B,hBne,isPGroup_pCoreIn 2 I,rfl⟩,
      hI.2.1.trans hIN, fun h => hI.2.2 (hIN.trans h)⟩
  obtain ⟨R,hR⟩ := d.sylow_in_escape hN
  have hRT : (R : Subgroup N).map N.subtype ≤ (T : Subgroup G) := hR ▸ inf_le_left
  have hsetup := Chapter1.lemma_1_1_6 hBne (isPGroup_pCoreIn 2 I)
    B.le_normalizer (Subgroup.centralizer_le_normalizer _) le_rfl R T hRT
    hm.1 hzT (fun t ht => hzc t ht) hMc hm.2.le
    (fun Q hQ hTQ => Chapter1.mem_He_iff.mpr (hsource.ambient.evenCharacteristic T Q hQ hTQ))
  have hSNI : (R : Subgroup N) ≤ (N ⊓ Mc).subgroupOf N := by
    intro x hx
    exact ⟨x.property,hTMc (hRT (mem_map_of_mem N.subtype hx))⟩
  have hcoreS : (N ⊓ Mc).pCoreIn 2 ≤ planeSylow T ZS := by
    have hh := pCoreIn_le_sylow ((N ⊓ Mc).subgroupOf N) (R.subtype hSNI)
    rw [pCoreIn_subgroupOf 2 (N ⊓ Mc) N inf_le_left,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hSNI] at hh
    intro x hx
    have hxN : x ∈ N := (pCoreIn_le 2 (N ⊓ Mc) hx).1
    exact hR ▸ mem_map_of_mem N.subtype
      (hh (show (⟨x,hxN⟩ : N) ∈ ((N ⊓ Mc).pCoreIn 2).subgroupOf N from hx))
  have hcore : (N ⊓ Mc).pCoreIn 2 ≤ (I ⊓ Mc).pCoreIn 2 :=
    (le_inf (le_inf (hcoreS.trans ((le_sup_right.trans
      (d.residual_sup_planeSylow_le hI)).trans inf_le_right)) (pCoreIn_le 2 (N ⊓ Mc) |>.trans inf_le_right)) le_rfl).trans
      (inf_pCoreIn_le_of_le 2 (inf_le_inf_right Mc hIN))
  refine ⟨hI.1,⟨hsetup.mem_HeOver.1,hsetup.mem_HeOver.2.1,?_⟩,?_,hm.1,?_,?_,hm.2.le⟩
  · rw [hP]
    exact inf_le_left.trans hTMc
  · have hsmall := (inf_le_inf_left (Mc.pCoreIn 2) (centralizer_le hcore)).trans hsetup.core_centralizer_le
    have hMT : Mc.pCoreIn 2 ≤ (T : Subgroup G) := by
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc] using
        pCoreIn_le_sylow Mc (T.subtype hTMc)
    have hTN := inf_eq_sylow_map R T.isPGroup' hRT
    exact ((le_inf (inf_le_left.trans hMT) hsmall).trans_eq
      (hTN.trans hR)).trans ((le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right)
  · rw [hP]
    exact ⟨hzT, d.plane_le_centralizer (d.seed_le hz)⟩
  · intro s hs
    exact hzc s (hP ▸ hs).1

end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
