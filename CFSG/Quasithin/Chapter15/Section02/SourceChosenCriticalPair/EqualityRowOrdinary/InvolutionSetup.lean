module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.SelectionGeometry
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.InvolutionSetup

/-!
# The literal 1.1.5 hypotheses from ResidualInput

The original Sylow and central involution markings satisfy the genuine
1.1.6 normalizer argument. This supplies the exact ordinary-component
consumer input without a plane-uniqueness packet or a partner residual identity.

Source: Aschbacher--Smith 15.2.20(1), printed p.1113, refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {h : ChosenSmallSource T M Mc V}
variable (r : ResidualInput h H B)
include r

/-- Original 15.2.20(1), with the literal central involution and Sylow subgroup of I. -/
theorem ResidualInput.lemma115_direct {I : Subgroup G} (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = planeSylow T ⁅V,B⁆)
    {z : G} (hz : z ∈ centralInvolutions T) (hne : z ≠ 1) :
    Chapter1.Lemma115Hypotheses I P Mc z := by
  have hm := r.marked_centralizer_of_seed_card (r.escape_index hI).1 hz hne
  have hzT := centralInvolutions_le_sylow T hz
  have hzc := centralInvolutions_le_centralizer_sylow T hz
  have hMc : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      h.partner ▸ Set.mem_singleton Mc).1
  have hTMc : (T : Subgroup G) ≤ Mc := by
    rw [← hm.2]
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (hzc t ht)
  let Q := I.pCoreIn 2
  have hQne : Q ≠ ⊥ := hI.1
  have hIN : I ≤ normalizer (Q : Set G) := by
    simpa only [Q,pCoreIn,normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using
      (pCore 2 I).le_normalizer_map I.subtype
  let N := normalizer (Q : Set G)
  have hN : PlaneEscapes Mc ⁅V,B⁆ N :=
    ⟨Chapter1.mem_H_of_isTwoLocal ⟨Q,hQne,isPGroup_pCoreIn 2 I,rfl⟩,
      hI.2.1.trans hIN, fun h => hI.2.2 (hIN.trans h)⟩
  obtain ⟨R,hR⟩ := r.sylow_in_escape hN
  change (R : Subgroup N).map N.subtype = planeSylow T ⁅V,B⁆ at hR
  have hRT : (R : Subgroup N).map N.subtype ≤ (T : Subgroup G) := hR ▸ inf_le_left
  have hsetup := Chapter1.lemma_1_1_6 hQne (isPGroup_pCoreIn 2 I)
    Q.le_normalizer (Subgroup.centralizer_le_normalizer _) le_rfl R T hRT
    hm.1 hzT (fun t ht => hzc t ht) hMc hm.2.le
    (fun Q hQ hTQ => Chapter1.mem_He_iff.mpr (h.ambient.evenCharacteristic T Q hQ hTQ))
  have hSNI : (R : Subgroup N) ≤ (N ⊓ Mc).subgroupOf N := by
    intro x hx
    exact ⟨x.property,hTMc (hRT (mem_map_of_mem N.subtype hx))⟩
  have hcoreS : (N ⊓ Mc).pCoreIn 2 ≤ planeSylow T ⁅V,B⁆ := by
    have hh := pCoreIn_le_sylow ((N ⊓ Mc).subgroupOf N) (R.subtype hSNI)
    rw [pCoreIn_subgroupOf 2 (N ⊓ Mc) N inf_le_left,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hSNI] at hh
    intro x hx
    have hxN : x ∈ N := (pCoreIn_le 2 (N ⊓ Mc) hx).1
    exact hR ▸ mem_map_of_mem N.subtype
      (hh (show (⟨x,hxN⟩ : N) ∈ ((N ⊓ Mc).pCoreIn 2).subgroupOf N from hx))
  have hcore : (N ⊓ Mc).pCoreIn 2 ≤ (I ⊓ Mc).pCoreIn 2 :=
    (le_inf (le_inf (hcoreS.trans ((le_sup_right.trans
      (r.residual_sup_planeCentralizer_le hI)).trans inf_le_right)) (pCoreIn_le 2 (N ⊓ Mc) |>.trans inf_le_right)) le_rfl).trans
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
      (hTN.trans hR)).trans ((le_sup_right.trans (r.residual_sup_planeCentralizer_le hI)).trans inf_le_right)
  · rw [hP]
    exact ⟨hzT, r.plane_le_centralizer_direct (r.seed_le_plane hz)⟩
  · intro s hs
    exact hzc s (hP ▸ hs).1


end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
