module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ComponentExtraction.Commutators
public import Theory.GroupTheory.PrimeRankResidualCentralizer
/-!
# Quintic rank of the extracted component

Pass the actual component and second factor to N_G(K_2)/O_2(N_G(K_2)).
Their images commute. A.3.6 bounds the quasisimple image's center by
one or three, so their five-ranks add. The exchanged factor supplies
an order-five element; the ambient SQTK bound therefore leaves the
component five-rank at most one. Two-group kernels preserve these ranks.

This is the rank inequality in Aschbacher--Smith 14.6.15, printed p.1035.
The subsequent residual identification, intersection normalization and
marked model comparisons are not asserted here.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExtraction
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open ComponentExclusion Chapter1.RadicalExclusions
variable {G : Type*} [Group G] [Finite G]

private theorem quasisimple_center_card (hs : IsSQTK KnownSimple.IsKnownSimple G)
    [IsQuasisimple G] (hc : pCore 2 G = ⊥) :
    Nat.card (center G) = 1 ∨ Nat.card (center G) = 3 := by
  have htop : (⊤ : Subgroup G).IsCComponent :=
    (show IsComponent G ⊤ from ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  have h := (ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) G hs hc ⊤ htop).2
  let : IsQuasisimple (⊤ : Subgroup G) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have hh := ChapterA.SQTKStructure.NonnormalOuterSource.FourModels.center_card_of_common h
  simpa only [Nat.card_congr (centerCongr (topEquiv : (⊤ : Subgroup G) ≃* G)).toEquiv] using hh

variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)
local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))
variable (d : NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative)


variable (J : Subgroup G) (hJN : J ≤ normalizer (d.K2 : Set G))
    (hJ : (J.subgroupOf (normalizer (d.K2 : Set G))).IsCComponent)
    (hq : IsQuasisimple (J ⧸ pCore 2 J))
    (hout : ¬J ≤ Mc ⊓ normalizer (d.K2 : Set G))

include hJN hJ hq hout in
/-- The actual escaping component has five-rank at most one. -/
theorem component_quintic_rank : primeRank 5 J ≤ 1 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let N := normalizer (d.K2 : Set G)
  let L := J.subgroupOf N
  let B := d.K2.subgroupOf N
  let e : L ≃* J := subgroupOfEquivOfLe hJN
  let : IsQuasisimple (L ⧸ pCore 2 L) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  let q := QuotientGroup.mk' (pCore 2 N)
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  let Q := N ⧸ pCore 2 N
  have hs := (source_secondNormalizer_setup s.ambient T s.empty s.maximal s.unique
    s.many s.module_card s.action s.abelian H s.outside a H1 H2 s.critical d).2.2
  have hQsq : IsSQTK KnownSimple.IsKnownSimple Q := by
    refine ⟨?_,hs.sqtk.isKGroup.quotient (pCore 2 N)⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 N) pCore_isPGroup).trans
      (hs.sqtk.stronglyQuasithin p hp ho)
  let : IsQuasisimple (L.map q) := IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hJ)
  have hsub : (L.map q).IsSubnormal := hJ.subnormal.map (QuotientGroup.mk'_surjective _)
  have hcore : pCore 2 (L.map q) = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hsub,pCore_quotient_pCore_eq_bot]
    exact (MonoidHom.ker_eq_bot_iff _).mpr (L.map q).subtype_injective
  have hcenter : Nat.Coprime 5 (Nat.card (center (L.map q))) := by
    rcases quasisimple_center_card (hQsq.subgroup (L.map q)) hcore with h | h <;>
      rw [h] <;> decide
  have hcomm : L.map q ≤ centralizer (B.map q : Set Q) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
    have hh := component_second_commutator s d J hJN hJ hq hout
    have hm : ⁅L,B⁆.map N.subtype ≤ J.pCoreIn 2 := by
      rwa [map_commutator,map_subgroupOf_eq_of_le hJN,
        map_subgroupOf_eq_of_le d.K2.le_normalizer]
    have hJcore : J.pCoreIn 2 = (L.pCoreIn 2).map N.subtype := by
      rw [map_pCoreIn_of_injective 2 L N.subtype N.subtype_injective,
        map_subgroupOf_eq_of_le hJN]
    rw [hJcore,map_le_map_iff_of_injective N.subtype_injective] at hm
    apply hm.trans
    rw [pCoreIn,pCore_subnormal_eq_comap 2 hJ.subnormal]
    exact Subgroup.map_comap_le _ _
  have hr := ResidualCentralizerRank.primeRank_add_le_of_center_coprime
    (B.map q) (L.map q) (le_centralizer_iff.mp hcomm) hcenter
  rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide : Odd 5) q hk,
    ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide : Odd 5) q hk,
    primeRank_congr 5 e,
    primeRank_congr 5 (subgroupOfEquivOfLe d.K2.le_normalizer)] at hr
  have hrQ : primeRank 5 Q ≤ 2 := hQsq.stronglyQuasithin 5 (by decide) (by decide)
  have hpos : 1 ≤ primeRank 5 d.K2 := by
    obtain ⟨k,hk,ho⟩ := exists_first_generator d
    obtain ⟨t,_,_,he⟩ := d.exchanged
    have ht : (MulAut.conj t⁻¹) k ∈ d.K2 := he ▸ mem_map_of_mem _ hk
    have ho' : orderOf (⟨(MulAut.conj t⁻¹) k,ht⟩ : d.K2) = 5 := by
      rw [←Subgroup.orderOf_coe,(MulAut.conj t⁻¹).orderOf_eq,ho]
    have hd : 5 ∣ Nat.card d.K2 := ho' ▸ orderOf_dvd_natCard (⟨(MulAut.conj t⁻¹) k,ht⟩ : d.K2)
    exact Nat.one_le_iff_ne_zero.mpr (fun hz => PrimeRank.eq_zero_iff_not_dvd_card.mp hz hd)
  change primeRank 5 (N ⧸ pCore 2 N) ≤ 2 at hrQ
  omega
/-- The C.2.6 extraction, C.2.4 alternative, commutator identities and
quintic rank bound hold for one and the same ambient component. -/
theorem exists_component_with_rank :
    ∃ J : Subgroup G, J ≤ normalizer (d.K2 : Set G) ∧
      (J.subgroupOf (normalizer (d.K2 : Set G))).IsCComponent ∧
      IsQuasisimple (J ⧸ pCore 2 J) ∧ generalizedFitting J = pCore 2 J ∧
      ¬J ≤ Mc ⊓ normalizer (d.K2 : Set G) ∧
      residualClosure H Mc ≤ normalizer (J : Set G) ∧
      J = ⁅J, residualClosure H Mc⁆ ∧ J = ⁅J, d.K1⁆ ∧ ⁅J, d.K2⁆ ≤ J.pCoreIn 2 ∧
      primeRank 5 J ≤ 1 ∧
      (Chapter1.IsSylowIn 2 (Mc.pCoreIn 2 ⊓ J) J ∨
        Mc.pCoreIn 2 ≤ normalizer (J : Set G)) := by
  obtain ⟨J, hJN, hJ, hq, hf, hout, hn, hz, hfirst, hsecond, ha⟩ :=
    exists_component_with_commutators s d
  exact ⟨J, hJN, hJ, hq, hf, hout, hn, hz, hfirst, hsecond,
    component_quintic_rank s d J hJN hJ hq hout, ha⟩
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExtraction
