module
public import Theory.SpecificGroups.ClassicalUnitary.OddFourProjectiveRank
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.UnitaryFour

/-!
# Excluding the last odd unitary-four normalizer component

The refined projective two-rank bound embeds the original full elementary
module in a group of rank at most five. The doubled odd-rank action forces
its order to be divisible by 64, a contradiction. The full covering center,
actual residual and original two-core quotient maps are retained.
Source: Aschbacher--Smith 4.4.3 and10.2.3(2), printed pp.622 and745.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- A placed odd PSU₄ component contradicts the full module order lower bound. -/
theorem source_nonnormal_oddNormalizer_no_placed_odd_unitary_four_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G))) (hc : pCore 2 K = ⊥)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    {r : ℕ} (ho : Odd r) (hm : ClassicalGroup.IsPSU (K ⧸ center K) 4 r) :
    False := by
  let S := L ⧸ pCore 2 L
  let := D.quasisimple
  let : IsSimpleGroup (S ⧸ center S) := IsQuasisimple.simple
  let : Nontrivial S := (QuotientGroup.mk'_surjective (center S)).nontrivial
  let N := normalizer (B : Set G)
  let F := (solvableResidual
    (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype
  let W := (D.fullModule.subgroupOf N).subgroupOf K
  have hVN : D.fullModule ≤ N := (le_centralizer_iff.mp hBV).trans
    (Subgroup.centralizer_le_normalizer _)
  obtain ⟨_,_,hVF⟩ := source_fullModule_oddActor_cover D B hBC hodd hBV
  have hVK : D.fullModule.subgroupOf N ≤ K :=
    (subgroupOf_mono N (hVF.trans (pCoreIn_le 2 F))).trans hFK
  obtain ⟨_,_,_,_,hW,_,_,_,_⟩ :=
    source_oddNormalizer_component_local_geometry_of_residual_le D B hBC hodd hBV K hFK
  have hup : Nat.card D.fullModule ≤ 32 := by
    rw [←Nat.card_congr ((subgroupOfEquivOfLe hVK).trans (subgroupOfEquivOfLe hVN)).toEquiv]
    exact elementary_card_le_of_twoCore_eq_bot W hW hc
      (by
        obtain ⟨F,_,_,J,hF,_,⟨e⟩⟩ := hm
        rw [primeRank_congr 2 e]
        exact Theory.SpecificGroups.ClassicalUnitary.odd_four_projective_twoRank_le_five J
          (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card ho hF))
  let := D.fullModule_elementary (Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal)
  have hdiv : 2^6 ∣ Nat.card D.fullModule :=
    ChapterC.HypothesisC28.elementary_sixtyFour_dvd_of_doubled_odd_ranks S D.fullModule (by
      intro p hp ho
      let : Fact p.Prime := ⟨hp⟩
      exact source_nonnormal_fullModule_automorphism_rank D hn ho)
  have hlo := Nat.le_of_dvd Nat.card_pos hdiv
  norm_num at hlo
  omega


/-- The actual Sylow Frattini bound places and excludes every escaping odd prime-field PSU₄ component. -/
theorem source_nonnormal_oddNormalizer_no_odd_unitary_four_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
    (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hc : pCore 2 K = ⊥) {r : ℕ} [Fact r.Prime] (ho : Odd r)
    (hm : ClassicalGroup.IsPSU (K ⧸ center K) 4 r) : False := by
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  exact source_nonnormal_oddNormalizer_no_placed_odd_unitary_four_component
    D hn B hBC hodd hBV K hc
    (source_nonnormal_oddNormalizer_unitary_four_residual_le D hn hp B hB hBC hBV hperm
      K hK hout ho hm) ho hm

end CFSG.Quasithin.Chapter10
