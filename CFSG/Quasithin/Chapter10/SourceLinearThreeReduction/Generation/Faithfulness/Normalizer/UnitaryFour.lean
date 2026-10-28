module
public import Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.SmallFrattini
public import CFSG.Quasithin.ChapterA.Section02.OddBModelTwoRank

/-!
# Residual placement and module order for odd PSU₄ components

The native Sylow Frattini bound places the original residual inside an
escaping odd-prime PSU₄ covering component. Its projective two-rank is at
most six. The full elementary module embeds through the covering center,
whereas its doubled odd-rank action forces its order to be divisible by 64.
Thus the original full module has order exactly 64.

Source: the PSU₄ row of Aschbacher--Smith Theorem B in the 4.4.3 argument,
printed p.622, as used in 10.2.3(2), printed p.745. This is a necessary
condition for this remaining row, not its exclusion.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The actual residual lies in every escaping odd prime-field PSU₄ covering component. -/
theorem source_nonnormal_oddNormalizer_unitary_four_residual_le
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
    (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    {r : ℕ} [Fact r.Prime] (ho : Odd r)
    (hm : ClassicalGroup.IsPSU (K ⧸ center K) 4 r) :
    ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K := by
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
  let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  apply source_nonnormal_oddNormalizer_residual_le_of_smallFrattini
    D hn hp B hB hBC hBV hperm K hK hout P
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup _))]
  exact (Theory.SpecificGroups.ClassicalUnitary.OddFrattiniSixteen.projective_frattini_le
    J ho hF hconj (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card ho hF) Q).trans
    (by decide)

/-- A placed odd PSU₄ component forces the original full module to have order 64. -/
theorem source_nonnormal_oddNormalizer_placed_unitary_four_module_card
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G))) (hc : pCore 2 K = ⊥)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    {r : ℕ} (ho : Odd r) (hm : ClassicalGroup.IsPSU (K ⧸ center K) 4 r) :
    Nat.card D.fullModule = 64 := by
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
  have hup : Nat.card D.fullModule ≤ 64 := by
    rw [←Nat.card_congr ((subgroupOfEquivOfLe hVK).trans (subgroupOfEquivOfLe hVN)).toEquiv]
    exact elementary_card_le_of_twoCore_eq_bot W hW hc
      (ChapterA.Section02.odd_psu_four_twoRank_le_six ho hm)
  let := D.fullModule_elementary (Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal)
  have hdiv : 2^6 ∣ Nat.card D.fullModule :=
    ChapterC.HypothesisC28.elementary_sixtyFour_dvd_of_doubled_odd_ranks S D.fullModule (by
      intro p hp ho
      let : Fact p.Prime := ⟨hp⟩
      exact source_nonnormal_fullModule_automorphism_rank D hn ho)
  exact Nat.le_antisymm hup (Nat.le_of_dvd Nat.card_pos hdiv)

end CFSG.Quasithin.Chapter10
