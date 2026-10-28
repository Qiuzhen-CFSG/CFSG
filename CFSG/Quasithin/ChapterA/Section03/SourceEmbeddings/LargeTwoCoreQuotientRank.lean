module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuasisimpleContaining
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.LargeTwoRankBender
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BenderSylowOvergroups
public import Theory.GroupTheory.PerfectCenterPrimeRank
/-!
# Cubic rank in proper local overcomponents with a surviving large two-section

A rank-four elementary section and a factor of five in the two-core quotient
force its component to be quasisimple. If cubic rank is at most one, its
central triple-cover alternative is impossible and the genuine Theorem C
catalogue reduces to a Bender carrier. Its proper full-Sylow overgroups are
solvable, contradicting a proper local C-component upstairs.

Source: the rank obstruction in Aschbacher--Smith 10.2.3(4), p.747,
using A.3.6 and the rank-one non-enlargement branch of A.3.12.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

theorem local_component_three_rank_of_large_twoCore_quotient
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hC : (⊤ : Subgroup G).IsCComponent)
    (S : Sylow 2 G) (L : Subgroup G) (hL : L ∈ localCComponents S) (hne : L ≠ ⊤)
    (h2 : 4 ≤ primeRank 2 (G ⧸ pCore 2 G))
    (h5 : 5 ∣ Nat.card (G ⧸ pCore 2 G)) : 2 ≤ primeRank 3 G := by
  by_contra! hsmall
  let Q := G ⧸ pCore 2 G
  have hQ : IsSQTK KnownSimple.IsKnownSimple Q := by
    refine ⟨?_,hG.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hG.stronglyQuasithin p hp ho)
  have ho : pCore 2 Q = ⊥ := pCore_quotient_pCore_eq_bot 2
  let := pCore_isNilpotent (p := 2) (G := G)
  have htop : (⊤ : Subgroup Q).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using
      hC.map_quotient (pCore 2 G)
  have h2top : 4 ≤ primeRank 2 (⊤ : Subgroup Q) := by
    rwa [primeRank_equiv 2 (topEquiv (G := Q))]
  let : IsQuasisimple (⊤ : Subgroup Q) :=
    NoncentralFitting.quasisimple_of_two_le_two_rank hQ ho htop (by omega)
  have h3top : primeRank 3 (⊤ : Subgroup Q) ≤ 1 := by
    rw [primeRank_equiv 3 (topEquiv (G := Q))]
    exact (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans
      (by omega)
  have hb : ClassificationModels.IsBenderModel (⊤ : Subgroup Q) := by
    rcases quasisimple_containing_component_models_knownSimple hQ ho htop with
      ⟨_,hm⟩ | ⟨⟨ez⟩,_⟩
    · exact bender_of_large_twoRank_low_threeRank_five hm h2top h3top
        (by rwa [Nat.card_congr (topEquiv (G := Q)).toEquiv])
    · have hz : Nat.card (center (⊤ : Subgroup Q)) = 3 := by
        rw [Nat.card_congr ez.toEquiv]
        simp
      have hp : IsPGroup 3 (center (⊤ : Subgroup Q)) := IsPGroup.of_card (n := 1) (by simpa using hz)
      have hnz : center (⊤ : Subgroup Q) ≠ ⊥ := by
        intro he
        rw [he,card_bot] at hz
        contradiction
      have hr := two_le_primeRank_of_nontrivial_prime_center (by decide : Odd 3) hp hnz
      omega
  have hproper : ∀ (T : Sylow 2 G) (P : Subgroup G),
      (T : Subgroup G) ≤ P → P ≠ ⊤ → Group.IsSolvable P := by
    apply isSolvable_proper_sylow_overgroup_of_twoCore_quotient
    exact isSolvable_proper_sylow_overgroup_of_equiv (topEquiv (G := Q)).symm
      (bender_solvable_proper_sylow_overgroup hb)
  have he := eq_of_solvable_sylow_overgroups S hL hC le_top
    (isSolvable_proper_sylow_overgroup_of_equiv (topEquiv (G := G)) hproper)
  exact hne he
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
