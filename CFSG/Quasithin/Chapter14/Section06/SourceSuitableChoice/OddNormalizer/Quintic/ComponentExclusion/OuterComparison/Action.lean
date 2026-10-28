module
public import Theory.GroupTheory.PCoreNormalizerAction
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ComponentExtraction.RankNormal

/-!
# The actual order-five action on the escaping component

Commutator generation supplies a first-factor generator acting nontrivially
on J/O₂(J). Its action has order five. At five-rank zero, divisibility of
orders rules out an inner action, and the actual outer class also has order
five. An outside generator alone is never used to establish outer action.

For a model whose outer group has order prime to five, this forces five-rank
one. The proved rank-normality theorem then supplies the literal C.2.7 input.
The outer-group order condition must be verified for the actual model; it is
not a classification callback. No rank-one outer-action exclusion is asserted.

The geometry and remaining model comparisons stay with
qt-e-14615-quintic-exclusion, whose final assembly proves p = 3. Earlier
14.6.12--14 source inputs stay with qt-e-suitable-odd-normalizer.
Source: Aschbacher--Smith 14.6.15, printed p.1035.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExtraction
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open ComponentExclusion Chapter1.RadicalExclusions
open ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
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
    (J : Subgroup G) (hJN : J ≤ normalizer (d.K2 : Set G))
    (hJ : (J.subgroupOf (normalizer (d.K2 : Set G))).IsCComponent)
    (hq : IsQuasisimple (J ⧸ pCore 2 J))
    (hout : ¬J ≤ Mc ⊓ normalizer (d.K2 : Set G))

include hJN hJ hq hout in
/-- Commutator generation gives an order-five actor on the literal core quotient. -/
theorem exists_first_generator_with_quotient_order :
    ∃ k : normalizer (J : Set G), (k : G) ∈ d.K1 ∧ orderOf k = 5 ∧
      orderOf (pCoreNormalizerAction 2 J k) = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hK : d.K1 ≤ normalizer (J : Set G) :=
    (show d.K1 ≤ residualClosure H Mc from d.join_eq ▸ le_sup_left).trans
      (closure_normalizes_component s d J hJN hJ hq)
  have hp : pCore 2 J ≠ ⊤ := by
    let : IsSimpleGroup ((J ⧸ pCore 2 J) ⧸ center (J ⧸ pCore 2 J)) := hq.simple
    let : Nontrivial (J ⧸ pCore 2 J) := (QuotientGroup.mk'_surjective (center _)).nontrivial
    exact QuotientGroup.nontrivial_iff.mp inferInstance
  obtain ⟨k,ho,hm⟩ := exists_prime_generator_nontrivial_core_action 2 J d.K1 hK
    d.first_generated (component_generated_by_first s d J hJN hJ hq hout) hp
  have hoN : orderOf (inclusion hK k) = 5 :=
    ((normalizer (J : Set G)).orderOf_coe _).symm.trans ((d.K1.orderOf_coe k).trans ho)
  refine ⟨inclusion hK k,k.property,hoN,orderOf_eq_prime ?_ hm⟩
  rw [←map_pow,←hoN,pow_orderOf_eq_one,map_one]

include hJN hJ hq hout in
/-- At five-rank zero, this actual generator and its outer class both have order five. -/
theorem exists_outer_quintic_of_rank_zero (hr : primeRank 5 J = 0) :
    ∃ k : normalizer (J : Set G), (k : G) ∈ d.K1 ∧ (k : G) ∉ J ∧
      orderOf k = 5 ∧ orderOf (pCoreNormalizerAction 2 J k) = 5 ∧
      pCoreNormalizerAction 2 J k ∉ MulAut.innerSubgroup (J ⧸ pCore 2 J) ∧
      orderOf (pCoreNormalizerOuterAction 2 J k) = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hc : ¬5 ∣ Nat.card J := PrimeRank.eq_zero_iff_not_dvd_card.mp hr
  obtain ⟨k,hk,ho,ha⟩ := exists_first_generator_with_quotient_order s d J hJN hJ hq hout
  have hi : pCoreNormalizerAction 2 J k ∉ MulAut.innerSubgroup (J ⧸ pCore 2 J) :=
    MulAut.prime_order_not_inner_of_not_dvd_card _ ha
      (fun hd => hc (hd.trans (card_quotient_dvd_card _)))
  refine ⟨k,hk,?_,ho,ha,hi,?_⟩
  · intro hkJ
    have hoJ : orderOf (⟨k,hkJ⟩ : J) = 5 :=
      (J.orderOf_coe _).symm.trans (((normalizer (J : Set G)).orderOf_coe k).trans ho)
    exact hc (hoJ ▸ orderOf_dvd_natCard (⟨k,hkJ⟩ : J))
  · exact MulAut.outer_order_eq_prime_of_prime_order_not_inner _ ha hi

include hJN hJ hq hout in
/-- The rank-zero branch forces five to divide the actual outer automorphism group order. -/
theorem five_dvd_outer_card_of_rank_zero (hr : primeRank 5 J = 0) :
    5 ∣ Nat.card (MulAut.Outer (J ⧸ pCore 2 J)) := by
  obtain ⟨k,_,_,_,_,_,ho⟩ := exists_outer_quintic_of_rank_zero s d J hJN hJ hq hout hr
  exact ho ▸ orderOf_dvd_natCard (pCoreNormalizerOuterAction 2 J k)

include hJN hJ hq hout in
/-- A model with no outer five-elements forces five-rank one on the extracted component. -/
theorem component_rank_one_of_outer_card_not_five
    (ho : ¬5 ∣ Nat.card (MulAut.Outer (J ⧸ pCore 2 J))) : primeRank 5 J = 1 := by
  have hr := component_quintic_rank s d J hJN hJ hq hout
  have hn : primeRank 5 J ≠ 0 := fun hz =>
    ho (five_dvd_outer_card_of_rank_zero s d J hJN hJ hq hout hz)
  omega

include hJN hJ hq hout in
/-- The same model condition supplies relative normality in the second normalizer. -/
theorem component_normal_of_outer_card_not_five
    (ho : ¬5 ∣ Nat.card (MulAut.Outer (J ⧸ pCore 2 J))) :
    (J.subgroupOf (normalizer (d.K2 : Set G))).Normal :=
  component_normal_of_quintic_rank_one s d J hJN hJ hq hout
    (component_rank_one_of_outer_card_not_five s d J hJN hJ hq hout ho)

include hJN hJ hq hout in
/-- Apply the rank and action argument to the original C.2.7 input. -/
theorem component_input_of_outer_card_not_five
    (hf : generalizedFitting J = pCore 2 J)
    (ho : ¬5 ∣ Nat.card (MulAut.Outer (J ⧸ pCore 2 J))) :
    Input KnownSimple.IsKnownSimple (normalizer (d.K2 : Set G)) (Mc.pCoreIn 2)
      (Mc ⊓ normalizer (d.K2 : Set G)) J := by
  have hs := (source_secondNormalizer_setup s.ambient T s.empty s.maximal s.unique
    s.many s.module_card s.action s.abelian H s.outside a H1 H2 s.critical d).2.2
  let := component_normal_of_outer_card_not_five s d J hJN hJ hq hout ho
  exact ⟨hs,⟨hJN,hJ⟩,hq,hf,hout,
    hs.radical_le.trans (le_normalizer_of_normal_subgroupOf hJN)⟩
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExtraction
