module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.Source
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.SourceApplication
public import Theory.GroupTheory.CentralInvolutionMarking
public import Theory.SpecificGroups.ReeTwo.ParabolicCentralInvolution

/-!
# Original-source rigidity for the Ree and Tits branches of 14.2.21

Suppose the actual outside subgroup H is isomorphic to the first full-Ree
or Tits parabolic. Its quotient by its two-core is Sz(2), so the source
Sylow subgroup is its intersection with M. The marked model involution is
central in H; since the original Sylow omega-center has order two, every
isomorphism carries this involution to the source mark.

Original 14.1.18 and 14.2.3 then supply the containing centralizer Mc,
its characteristic-two property and the residual decomposition of M.
The proved local rigidity gives H = Mc and hence M = YT. All source-local
and marking premises of the earlier conditional application are discharged.
Only the actual parabolic isomorphism, supplied by amalgam recognition in
this branch, remains beyond Hypothesis 14.2.1 and H in H*(T,M).

Source: Aschbacher--Smith 14.2.21, printed pp.988--989.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ReeTwo.ParabolicConcrete ReeTwo.Centralizer Tits.ExceptionalParabolics
variable {G : Type*} [Group G] [Finite G]

private theorem mark_of_equiv
    {A : Type*} [Group A] (z : A) (hz : z ∈ center A) (ho : orderOf z = 2)
    (T : Sylow 2 G) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hZ : Nat.card (centralInvolutions T) = 2) (e : A ≃* H) :
    zpowers (e z : G) = centralInvolutions T := by
  apply central_involution_marking T H hTH hZ (e z) _ ((e.orderOf_eq z).trans ho)
  apply mem_center_iff.mpr
  intro h
  obtain ⟨a,rfl⟩ := e.surjective h
  simpa only [map_mul] using congrArg e (mem_center_iff.mp hz a)

/-- The Ree/Tits part of original 14.2.21, from the literal unmarked
parabolic recognition and the original plane-source hypotheses. -/
theorem source_ree_tits_rigidity
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hmodel : Nonempty (FullRee.first ≃* H) ∨
      Nonempty (Tits.ExceptionalParabolics.first ≃* H)) :
    H = Mc ∧ M = sourceResidual M Mc ⊔ (T : Subgroup G) := by
  have hZ := plane_centralInvolutions_card T M hM.1.2 hcard e
  obtain ⟨_,hne,hMc,_⟩ := plane_ordering_and_overgroups hG T hempty hM hu hmany hcard hZ
  have hHMc : H ≤ Mc := hMc ▸
    (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hTMc : (T : Subgroup G) ≤ Mc := hTH.trans hHMc
  have hMcMem : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hc : centralizer (pCore 2 Mc : Set Mc) ≤ pCore 2 Mc :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T)
      ⟨Chapter1.mem_H_of_isTwoLocal hMcMem.1.1,hTMc⟩)
  have hq : SmallSolvableModel (H ⧸ pCore 2 H) := by
    apply Or.inr ∘ Or.inl
    rcases hmodel with hd | hd
    · obtain ⟨d⟩ := hd
      exact ⟨(QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm.trans
        FullRee.firstCoreQuotientEquiv⟩
    · obtain ⟨d⟩ := hd
      exact ⟨(QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm.trans
        FirstQuotient.coreQuotientEquiv⟩
  have hint : H ⊓ M = (T : Subgroup G) := by
    have hh := (sylow_normalizer_small_core_quotient (T.subtype hTH) hq.card).2
      (M.subgroupOf H) (fun x hx => hM.1.2 hx) (lt_top_iff_ne_top.mpr (by
        intro ht
        apply hH.1.2
        intro x hx
        exact show (⟨x,hx⟩ : H) ∈ M.subgroupOf H from ht.ge (mem_top _)))
    have hm := congrArg (Subgroup.map H.subtype) hh
    rw [subgroupOf_map_subtype,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,inf_comm] at hm
    exact hm
  obtain ⟨_,hnoncentral,_⟩ :=
    plane_intersection_core_inputs hG T hempty hM.1 hu hmany hZ hne
  apply rigidity_and_factorization H M Mc (sourceResidual M Mc) (T : Subgroup G)
    (centralInvolutions T) (localModule T M) hHMc _ hMc (T.subtype hTMc)
    (fun x hx => hTH hx) hc hint (le_conjugateSpanBy _ _)
    (decomposition_of_intersectionCore_not_centralizing M Mc (localModule T M) T
      hM.1.2 ⟨e⟩ hnoncentral).le (sourceResidual_le _ _) hM.1.2
  rcases hmodel with hd | hd
  · obtain ⟨d⟩ := hd
    exact Or.inl ⟨d,mark_of_equiv _ ree_marked_central_involution.1
      ree_marked_central_involution.2 T H hTH hZ d⟩
  · obtain ⟨d⟩ := hd
    exact Or.inr ⟨d,mark_of_equiv _ tits_marked_central_involution.1
      tits_marked_central_involution.2 T H hTH hZ d⟩

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal
