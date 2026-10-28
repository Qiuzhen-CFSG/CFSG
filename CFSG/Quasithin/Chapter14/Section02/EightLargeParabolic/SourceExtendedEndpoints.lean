module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCubic

/-!
# Exact intersections and faithful original endpoint extensions

The F.1.3 cross-normalizer equality identifies the second endpoint's
intersection with Mc. The actual cubic supplement is consequently disjoint
from both original endpoints. Any subgroup of the whole enlarged overlap
normal in both enlarged endpoints is trivial, by F.1.1 and characteristic two.
No marked model or ambient-generation assumption is required.

Source: Aschbacher--Smith F.1.3(2) and 14.2.18, printed pp.260,987.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceExtendedEndpoints
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR

private theorem first_residual : residual H = H := by
  rw [residual, SourcePerfect.first_twoResidual_eq_top hG T hempty hM hu hmany hcard e H hH eR,
    ← MonoidHom.range_eq_map, range_subtype]

omit eR in
private theorem second_partner_factorization :
    M = (sourceResidual M Mc ⊔ (T : Subgroup G)) ⊔ (M ⊓ Mc) := by
  have hne : M ≠ Mc := by
    intro he
    exact hH.1.2 (he.symm ▸ source_first_le_partner hG hempty hM hu hmany hcard e hH)
  have hZ := plane_centralInvolutions_card T M hM.1.2 hcard e
  have hc := (plane_intersection_core_inputs hG T hempty hM.1 hu hmany hZ hne).2.1
  have hd := decomposition_of_intersectionCore_not_centralizing
    M Mc (localModule T M) T hM.1.2 ⟨e⟩ hc
  apply le_antisymm
  · calc
      M = (sourceResidual M Mc ⊔ (T : Subgroup G)) ⊔
          (M ⊓ centralizer (localModule T M : Set G)) := hd
      _ ≤ (sourceResidual M Mc ⊔ (T : Subgroup G)) ⊔ (M ⊓ Mc) :=
        sup_le le_sup_left ((le_inf inf_le_left
          (inf_le_right.trans (InitialSource.localModule_centralizer_le_partner T M hu))).trans le_sup_right)
  · exact sup_le (sup_le (sourceResidual_le M Mc) hM.1.2) inf_le_left


/-- The second endpoint meets the original partner in exactly the whole base Borel. -/
theorem second_inf_partner :
    secondParabolic T M Mc H ⊓ Mc = H ⊓ M := by
  let L := locals T M Mc H
  let B := ChapterF.Source.commonBorel L (T : Subgroup G)
  have hf := (source_hypothesis hG T hempty hM hu hmany hcard e H hH
    eR).1
  obtain ⟨h0,h1,hB,hinter,hPM⟩ := source_parabolics
    hG T hempty hM hu hmany hcard e H hH eR
  have hBH : B ≤ normalizer (H : Set G) := by
    have h := hf.commonBorel_normalizes_local 0
    change B ≤ normalizer (residual H : Set G) at h
    rwa [first_residual hG T hempty hM hu hmany hcard e H hH eR] at h
  have hB1 : ChapterF.Source.borel (L 1) (T : Subgroup G) =
      L 1 ⊓ normalizer (H : Set G) := by
    have h := ChapterF.Source.lemma_F_1_3_2 hf 0
    change ChapterF.Source.borel (L 1) (T : Subgroup G) =
      L 1 ⊓ normalizer (residual H : Set G) at h
    rwa [first_residual hG T hempty hM hu hmany hcard e H hH eR] at h
  have hprod : secondParabolic T M Mc H = L 1 ⊔ B := by
    rw [←h1]
    exact ChapterF.Source.parabolic_eq_sup_commonBorel _ _ 1
  apply le_antisymm
  · intro x hx
    have hxN : x ∈ normalizer (H : Set G) :=
      SourceNormal.partner_le_first_normalizer hG T hempty hM hu hmany hcard e H hH eR hx.2
    have hxprod : x ∈ (L 1 : Set G) * (B : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left _ _ (hf.commonBorel_normalizes_local 1), ←hprod]
      exact hx.1
    obtain ⟨a,ha,b,hb,rfl⟩ := hxprod
    have haN := (normalizer _).mul_mem_cancel_right (hBH hb) |>.mp hxN
    have haB : a ∈ B := ChapterF.Source.borel_le_commonBorel 1
      (hB1.symm ▸ (show a ∈ L 1 ⊓ normalizer (H : Set G) from ⟨ha,haN⟩))
    exact hB ▸ B.mul_mem haB hb
  · rw [←hinter]
    exact le_inf inf_le_right (inf_le_left.trans
      (source_first_le_partner hG hempty hM hu hmany hcard e hH))

/-- If the original partner is H, the second endpoint is the full M. -/
theorem second_eq_of_partner_eq
    (he : Mc = H) : secondParabolic T M Mc H = M := by
  have h := second_partner_factorization hG T hempty hM hu hmany hcard e H hH
  simpa only [he,secondParabolic,first_residual hG T hempty hM hu hmany hcard e H hH eR] using h.symm

omit [Finite G] hG hempty hM hu hmany hcard e hH eR in
private theorem disjoint_of_prime_supplement {X A E : Subgroup G}
    (hcardA : Nat.card A = 3) (hgen : E = X ⊔ A) (hne : E ≠ X) : Disjoint X A := by
  let : Fact (Nat.card A).Prime := ⟨by rw [hcardA]; decide⟩
  rcases (X.subgroupOf A).eq_bot_or_eq_top_of_prime_card with hb | ht
  · have hm := congrArg (Subgroup.map A.subtype) hb
    rw [subgroupOf_map_subtype,Subgroup.map_bot] at hm
    exact disjoint_iff.mpr hm
  · have hAX : A ≤ X := by
      intro a ha
      exact show (⟨a,ha⟩ : A) ∈ X.subgroupOf A from ht ▸ mem_top _
    exact (hne (hgen.trans (sup_eq_left.mpr hAX))).elim

/-- A proper partner gives one cubic subgroup disjoint from both base endpoints. -/
theorem split_endpoint_data (hne : Mc ≠ H) :
    ∃ A : Subgroup G,
      A ≤ M ⊓ Mc ∧ Nat.card A = 3 ∧
      A ≤ normalizer (H : Set G) ∧
      A ≤ normalizer (secondParabolic T M Mc H : Set G) ∧
      Disjoint H A ∧ Disjoint (secondParabolic T M Mc H) A ∧
      Mc = H ⊔ A ∧ M = secondParabolic T M Mc H ⊔ A ∧
      Mc ⊓ M = (H ⊓ secondParabolic T M Mc H) ⊔ A := by
  rcases SourceCubic.cubic_endpoint_factorizations hG T hempty hM hu hmany hcard e H hH eR with
    he | ⟨A,hA,hcardA,hMc,hI,hMP,hAP,hprod,hprodM⟩
  · exact (hne he).elim
  have hAH := (hA.trans inf_le_right).trans
    (SourceNormal.partner_le_first_normalizer hG T hempty hM hu hmany hcard e H hH eR)
  have hdH := disjoint_of_prime_supplement hcardA hMc hne
  have hdP : Disjoint (secondParabolic T M Mc H) A := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    have hxH : x ∈ H := ((second_inf_partner
      hG T hempty hM hu hmany hcard e H hH eR).le ⟨hx.1,(hA hx.2).2⟩).1
    exact (disjoint_iff.mp hdH).le ⟨hxH,hx.2⟩
  refine ⟨A,hA,hcardA,hAH,hAP,hdH,hdP,hMc,hMP,?_⟩
  rw [inf_comm Mc M,hI, (source_parabolics hG T hempty hM hu hmany hcard e
    H hH eR).2.2.2.1, inf_comm H M]

/-- The whole enlarged overlap contains no nontrivial subgroup normal in both endpoints. -/
theorem extended_common_normal_eq_bot
    (N : Subgroup G) (hN : N ≤ Mc ⊓ M)
    (hNc : Mc ≤ normalizer (N : Set G)) (hNM : M ≤ normalizer (N : Set G)) : N = ⊥ := by
  have hHM := source_first_le_partner hG hempty hM hu hmany hcard e hH
  obtain ⟨_,_,_,hinter,hPM⟩ := source_parabolics
    hG T hempty hM hu hmany hcard e H hH eR
  have hinf : N ⊓ H = N ⊓ secondParabolic T M Mc H := by
    apply le_antisymm
    · intro x hx
      exact ⟨hx.1,(hinter.symm ▸ (show x ∈ H ⊓ M from ⟨hx.2,(hN hx.1).2⟩)).2⟩
    · intro x hx
      exact ⟨hx.1,((second_inf_partner hG T hempty hM hu hmany hcard e H hH eR).le
        ⟨hx.2,(hN hx.1).1⟩).1⟩
  have hbot : N ⊓ H = ⊥ := by
    apply (source_completion hG T hempty hM hu hmany hcard e H hH
      eR).2
    · exact le_inf inf_le_right (hinf ▸ (show N ⊓ secondParabolic T M Mc H ≤
        secondParabolic T M Mc H from inf_le_right))
    · exact (le_inf (hHM.trans hNc) H.le_normalizer).trans inf_normalizer_le_normalizer_inf
    · rw [hinf]
      exact (le_inf (hPM.trans hNM) (secondParabolic T M Mc H).le_normalizer).trans
        inf_normalizer_le_normalizer_inf
  have hcomm : ⁅N,H⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [←hbot]
    exact le_inf
      (le_normalizer_iff_commutator_le_left.mp (hHM.trans hNc))
      (le_normalizer_iff_commutator_le_right.mp ((hN.trans inf_le_left).trans
        (SourceNormal.partner_le_first_normalizer hG T hempty hM hu hmany hcard e H hH eR)))
  have hC := commutator_eq_bot_iff_le_centralizer.mp hcomm
  apply bot_unique
  intro n hn
  have hnq : (⟨n,(hN hn).1⟩ : Mc) ∈ pCore 2 Mc := by
    apply source_partner_characteristic_two hG hempty hM hu hmany hcard e hH
    intro q hq
    apply Subtype.ext
    apply (hC hn)
    apply pCoreIn_le 2 H
    rw [←SourcePartnerCore.partner_core_eq hG T hempty hM hu hmany hcard e H hH eR]
    exact ⟨q,hq,rfl⟩
  have hnH : n ∈ H := by
    apply pCoreIn_le 2 H
    rw [←SourcePartnerCore.partner_core_eq hG T hempty hM hu hmany hcard e H hH eR]
    exact ⟨⟨n,(hN hn).1⟩,hnq,rfl⟩
  exact hbot.le ⟨hn,hnH⟩

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceExtendedEndpoints
