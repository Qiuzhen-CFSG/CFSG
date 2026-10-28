module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ComponentExtraction.Rank
public import Theory.GroupTheory.CComponent.RankComplementNormal
import all CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ComponentExtraction.Rank
/-!
# Relative normality of the rank-one escaping component

K₂ is normal in its actual normalizer and has positive five-rank. The
escaping component commutes with it modulo the ambient two-core. A.3.6
bounds the component quotient's center by one or three. Thus a second
component conjugate would force five-rank at least three, contrary to SQTK.
Normality in the quotient lifts back to the original component.

This intentionally internal extension reuses Rank's private center-card
lemma. It proves relative normality directly; no identification with a
residual of a full centralizer is needed. The Contained extension applies
it to the actual C.2.7 input and marked natural-row comparison.

Source: Aschbacher--Smith 14.6.15, printed p.1035. Construction of the
NormalizerGeometry premise remains with qt-e-14615-quintic-exclusion.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExtraction
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open ComponentExclusion Chapter1.RadicalExclusions
variable {G : Type*} [Group G] [Finite G]

private theorem core_quotient_sqtk (hs : IsSQTK KnownSimple.IsKnownSimple G) :
    IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G) := by
  refine ⟨?_,hs.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (hs.stronglyQuasithin p hp ho)

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

/-- An exchanged order-five generator survives in the actual normal factor. -/
theorem second_quintic_rank_pos : 1 ≤ primeRank 5 d.K2 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨k,hk,ho⟩ := exists_first_generator d
  obtain ⟨t,_,_,he⟩ := d.exchanged
  have ht : (MulAut.conj t⁻¹) k ∈ d.K2 := he ▸ mem_map_of_mem _ hk
  have ho' : orderOf (⟨(MulAut.conj t⁻¹) k,ht⟩ : d.K2) = 5 := by
    rw [←Subgroup.orderOf_coe,(MulAut.conj t⁻¹).orderOf_eq,ho]
  have hd : 5 ∣ Nat.card d.K2 := ho' ▸ orderOf_dvd_natCard (⟨(MulAut.conj t⁻¹) k,ht⟩ : d.K2)
  exact Nat.one_le_iff_ne_zero.mpr (fun hz => PrimeRank.eq_zero_iff_not_dvd_card.mp hz hd)

/-- Five-rank one makes the extracted component normal in the second normalizer.
The proof uses the actual quotient ranks, without a residual-centralizer identity. -/
theorem component_normal_of_quintic_rank_one (J : Subgroup G)
    (hJN : J ≤ normalizer (d.K2 : Set G))
    (hJ : (J.subgroupOf (normalizer (d.K2 : Set G))).IsCComponent)
    (hq : IsQuasisimple (J ⧸ pCore 2 J))
    (hout : ¬J ≤ Mc ⊓ normalizer (d.K2 : Set G)) (hr : primeRank 5 J = 1) :
    (J.subgroupOf (normalizer (d.K2 : Set G))).Normal := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let N := normalizer (d.K2 : Set G)
  let L := J.subgroupOf N
  let B := d.K2.subgroupOf N
  let : B.Normal := inferInstance
  let e : L ≃* J := subgroupOfEquivOfLe hJN
  let : IsQuasisimple (L ⧸ pCore 2 L) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hs := (source_secondNormalizer_setup s.ambient T s.empty s.maximal s.unique
    s.many s.module_card s.action s.abelian H s.outside a H1 H2 s.critical d).2.2
  have hc : Nat.Coprime 5 (Nat.card (center (L ⧸ pCore 2 L))) :=
    by
      rcases quasisimple_center_card (core_quotient_sqtk (hs.sqtk.subgroup L))
        (pCore_quotient_pCore_eq_bot 2) with hc | hc <;> rw [hc] <;> decide
  have hm : ⁅L,B⁆ ≤ L.pCoreIn 2 := by
    apply (map_le_map_iff_of_injective N.subtype_injective).mp
    rw [map_commutator,map_pCoreIn_of_injective 2 L N.subtype N.subtype_injective,
      map_subgroupOf_eq_of_le hJN,map_subgroupOf_eq_of_le d.K2.le_normalizer]
    exact component_second_commutator s d J hJN hJ hq hout
  apply hJ.normal_of_coprime_core_center_rank_complement (by decide : Odd 5) B hc hm
  have hN : primeRank 5 N ≤ 2 := hs.sqtk.stronglyQuasithin 5 (by decide) (by decide)
  have hB : 1 ≤ primeRank 5 B := by
    rw [primeRank_congr 5 (subgroupOfEquivOfLe d.K2.le_normalizer)]
    exact second_quintic_rank_pos s d
  have hL : primeRank 5 L = 1 := (primeRank_congr 5 e).trans hr
  change primeRank 5 N < 2 * primeRank 5 L + primeRank 5 B
  omega
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExtraction
