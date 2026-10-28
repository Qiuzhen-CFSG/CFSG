module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalAction

/-!
# Size obstructions for a fixed local module

The local module retains both odd ranks of the original component. Its
embedding in an escaping component also survives the full covering center,
whose two-core is trivial. Consequently projective two-rank at most five
is impossible; two-rank at most seven is impossible when seven-rank is at
most one. These bounds apply to the actual Sylow-fixed orbit without any
assumption that the actor fixes its M-conjugates.

Source: Aschbacher--Smith 4.4.10--12 and 10.2.3(2), printed pp.621--623,745.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.LocalFixed
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  (V : Subgroup G) (hVV : V ≤ D.fullModule) (hne : V ≠ ⊥)
  (hVX : V = ⁅V,localOrbit T L⁆)
  (hNV : localJoin T L ≤ normalizer (V : Set G))
  (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
  (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (V : Set G))
  (K : Subgroup (normalizer (B : Set G)))
  (hc : pCore 2 K = ⊥)
  (hFK : ((solvableResidual
    (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
        (normalizer (B : Set G)) ≤ K)
include hVV hne hVX hNV hBC hodd hBV hc hFK

/-- Projective rank bounds apply to the original local module across the full center. -/
theorem source_local_module_card_le {d : ℕ}
    (hr : primeRank 2 (K ⧸ center K) ≤ d) : Nat.card V ≤ 2^d := by
  let N := normalizer (B : Set G)
  let F := (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
    (localOrbit T L ⊓ centralizer (B : Set G)).subtype
  let W := (V.subgroupOf N).subgroupOf K
  have hVN : V ≤ N := (le_centralizer_iff.mp hBV).trans
    (Subgroup.centralizer_le_normalizer _)
  obtain ⟨_,_,hVF⟩ := source_local_oddActor_cover D V hVV hVX hNV B hBC hodd hBV
  have hVK : V.subgroupOf N ≤ K :=
    (subgroupOf_mono N (hVF.trans (pCoreIn_le 2 F))).trans hFK
  obtain ⟨_,_,_,_,hW,_,_,_,_⟩ :=
    source_local_oddActor_component_geometry D V hVV hne hVX hNV B hBC hodd hBV K hFK
  rw [←Nat.card_congr ((subgroupOfEquivOfLe hVK).trans (subgroupOfEquivOfLe hVN)).toEquiv]
  exact elementary_card_le_of_twoCore_eq_bot W hW hc hr

include hn
/-- A projective two-rank bound of five contradicts the literal local pair action. -/
theorem source_no_component_of_rank_five
    (hr : primeRank 2 (K ⧸ center K) ≤ 5) : False := by
  have hup := source_local_module_card_le D V hVV hne hVX hNV B hBC hodd hBV K hc hFK hr
  let S := L ⧸ pCore 2 L
  let := D.quasisimple
  let : IsSimpleGroup (S ⧸ center S) := IsQuasisimple.simple
  let : Nontrivial S := (QuotientGroup.mk'_surjective (center S)).nontrivial
  let := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le hVV
  have hdiv : 2^6 ∣ Nat.card V :=
    ChapterC.HypothesisC28.elementary_sixtyFour_dvd_of_doubled_odd_ranks S V (by
      intro r hr hor
      let : Fact r.Prime := ⟨hr⟩
      exact source_local_automorphism_rank D hn V hVV hne hVX hNV hor)
  have hlo := Nat.le_of_dvd Nat.card_pos hdiv
  norm_num at hlo hup
  omega

/-- Small two-rank together with small seven-rank excludes the containing component. -/
theorem source_nonnormal_oddNormalizer_no_placed_small_rank_component
    (hr2 : primeRank 2 (K ⧸ center K) ≤ 7)
    (hr7 : primeRank 7 (K ⧸ center K) ≤ 1) : False := by
  let S := L ⧸ pCore 2 L
  let := D.quasisimple
  let : IsSimpleGroup (S ⧸ center S) := IsQuasisimple.simple
  let : Nontrivial S := (QuotientGroup.mk'_surjective (center S)).nontrivial
  obtain ⟨p,hp,ho,hp3,hd⟩ := Perfect.exists_odd_prime_ne_dvd_card S Nat.prime_three
  let : Fact p.Prime := ⟨hp⟩
  have hpos : 0 < primeRank p S := Nat.pos_of_ne_zero
    (fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he hd)
  have hp7 : p ≠ 7 := by
    intro he
    subst p
    obtain ⟨_,_,_,_,_,hr⟩ :=
      source_local_oddActor_component_quotient_geometry D hn V hVV hne hVX hNV B hBC hodd hBV K hFK
    have hlo : 2 * primeRank 7 S ≤ primeRank 7 (K ⧸ center K) :=
      (hr 7 hp ho).symm.le.trans (primeRank_subgroup_le 7 _)
    omega
  have hcard := source_local_module_card_le D V hVV hne hVX hNV B hBC hodd hBV K hc hFK hr2
  let := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le hVV
  have hlo := source_local_automorphism_rank D hn V hVV hne hVX hNV ho
  change 2 * primeRank p S ≤ primeRank p (MulAut V) at hlo
  have hup := primeRank_mulAut_le_one_of_card_le_two_pow_seven V hcard ho hp3 hp7
  omega

end CFSG.Quasithin.Chapter10.LocalFixed
