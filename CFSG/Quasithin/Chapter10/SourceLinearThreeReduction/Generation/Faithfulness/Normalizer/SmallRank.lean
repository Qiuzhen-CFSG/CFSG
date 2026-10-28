module
public import Theory.GroupTheory.ElementarySmallRankBounds
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.OrdinaryJankoFour

/-!
# Small-rank normal components in the actual odd-kernel normalizer

The full module embeds in a containing component's central quotient when
its two-core is trivial. Two-rank at most seven bounds its automorphism
ranks outside three and seven. The quotient's seven-rank bound excludes
seven too, contradicting the doubled odd ranks of the original perfect
component quotient. The native J₂, HS and Rudvalis bounds apply through
the literal component equivalence, with residual placement supplied by
outer solvability and covering uniqueness.

Source: Aschbacher--Smith 4.4.10--12 and 10.2.3(2), pp.621--623,745.
Module fixation remains with the Hall-faithfulness assembly.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- A small two-rank and small seven-rank exclude the actual containing cover. -/
theorem source_nonnormal_oddNormalizer_no_placed_small_rank_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G))) (hc : pCore 2 K = ⊥)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
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
      source_nonnormal_oddNormalizer_component_quotient_geometry D hn B hBC hodd hBV K hFK
    have hlo : 2 * primeRank 7 S ≤ primeRank 7 (K ⧸ center K) :=
      (hr 7 hp ho).symm.le.trans (primeRank_subgroup_le 7 _)
    omega
  let N := normalizer (B : Set G)
  let F := (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
    (localOrbit T L ⊓ centralizer (B : Set G)).subtype
  let W := (D.fullModule.subgroupOf N).subgroupOf K
  have hVN : D.fullModule ≤ N := (le_centralizer_iff.mp hBV).trans
    (Subgroup.centralizer_le_normalizer _)
  have hVK : D.fullModule.subgroupOf N ≤ K := by
    obtain ⟨_,_,hVF⟩ := source_fullModule_oddActor_cover D B hBC hodd hBV
    exact (subgroupOf_mono N (hVF.trans (pCoreIn_le 2 F))).trans hFK
  obtain ⟨_,_,_,_,hW,_,_,_,_⟩ :=
    source_oddNormalizer_component_local_geometry_of_residual_le D B hBC hodd hBV K hFK
  have hcard : Nat.card D.fullModule ≤ 2 ^ 7 := by
    rw [←Nat.card_congr ((subgroupOfEquivOfLe hVK).trans (subgroupOfEquivOfLe hVN)).toEquiv]
    exact elementary_card_le_of_twoCore_eq_bot W hW hc hr2
  let := D.fullModule_elementary (Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal)
  have hlo := source_nonnormal_fullModule_automorphism_rank D hn ho
  change 2 * primeRank p S ≤ primeRank p (MulAut D.fullModule) at hlo
  have hup := primeRank_mulAut_le_one_of_card_le_two_pow_seven
    D.fullModule hcard ho hp3 hp7
  omega

variable
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
  (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
  (hu : UniqueMaximalOvergroup
    ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype ⊔
      ((T : Subgroup G) ⊓ normalizer (B : Set G))) D.maximalLocal)
  (K : Subgroup (normalizer (B : Set G)))
  (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
  (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
  (hc : pCore 2 K = ⊥)
include D hn hBC hodd hBV hu hK hout hc

/-- J₂ is excluded with the literal component center and residual placement. -/
theorem source_nonnormal_oddNormalizer_no_jankoTwo_component
    (e : K ⧸ center K ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply source_nonnormal_oddNormalizer_no_placed_small_rank_component D hn B hBC hodd hBV K hc
    (source_nonnormal_oddNormalizer_residual_le_of_theoremC D hn B hBC hodd hBV hu K hK hout
      (.sporadic (Or.inl ⟨.j2, (by intro h; cases h), ⟨e⟩⟩)))
  · rw [primeRank_congr 2 e]
    exact Sporadic.LeechRelated.J2.primeRank_two_le_seven
  · rw [primeRank_congr 7 e]
    apply primeRank_le_one_of_square_not_dvd
    rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
    decide

/-- HS is excluded with the literal component center and residual placement. -/
theorem source_nonnormal_oddNormalizer_no_higmanSims_component
    (e : K ⧸ center K ≃* Sporadic.LeechRelated.HS.Carrier) : False := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply source_nonnormal_oddNormalizer_no_placed_small_rank_component D hn B hBC hodd hBV K hc
    (source_nonnormal_oddNormalizer_residual_le_of_theoremC D hn B hBC hodd hBV hu K hK hout
      (.sporadic (Or.inl ⟨.hs, (by intro h; cases h), ⟨e⟩⟩)))
  · rw [primeRank_congr 2 e]
    exact Sporadic.LeechRelated.HS.twoRank_le_four.trans (by decide)
  · rw [primeRank_congr 7 e]
    apply primeRank_le_one_of_square_not_dvd
    rw [Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier]
    decide

/-- Rudvalis is excluded with the literal component center and residual placement. -/
theorem source_nonnormal_oddNormalizer_no_rudvalis_component
    (e : K ⧸ center K ≃* Rudvalis.Model) : False := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply source_nonnormal_oddNormalizer_no_placed_small_rank_component D hn B hBC hodd hBV K hc
    (source_nonnormal_oddNormalizer_residual_le_of_theoremC D hn B hBC hodd hBV hu K hK hout
      (.sporadic (Or.inl ⟨.ru, (by intro h; cases h), ⟨e⟩⟩)))
  · rw [primeRank_congr 2 e]
    exact Rudvalis.primeRank_le_six.trans (by decide)
  · rw [primeRank_congr 7 e]
    apply primeRank_le_one_of_square_not_dvd
    rw [Rudvalis.model_card]
    decide

end CFSG.Quasithin.Chapter10
