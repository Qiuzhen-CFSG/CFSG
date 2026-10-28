module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.PerfectFactor
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SeventeenRankOne

/-!
# Excluding the exchanged component in the actual second normalizer

Perfectness of the original PSL₂(16) factor puts it in the escaping component
and forces five-rank one. Its simple quotient survives the solvable star
kernel, so 17 divides the actual star component. The full B.5.1 catalogue
then selects its natural moved-section row, including best offenders.
The established natural-row contradiction excludes this escaping component.

This completes the terminal exchanged-model comparison under the source
NormalizerGeometry. The construction of that geometry, the residual branch
and final p=3 assembly remain with qt-e-14615-quintic-exclusion. The literal
14.6.12--14 premises retain discharge with qt-e-suitable-odd-normalizer.
No full-centralizer residual identity or additional classification callback
is assumed.
Source: Aschbacher–Smith 14.6.15, p.1035, using C.2.7 and B.5.1.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped commutatorElement Pointwise IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open ComponentExclusion ComponentExtraction ComponentExclusion.ContainedComparison
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
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
    (j : SourceEscapingComponent Mc (residualClosure H Mc) d.K1 d.K2 (Mc.pCoreIn 2))


/-- Seventeen divisibility and five-rank one select the natural row on the
literal C.2.7 star representation, with its original quotient and offenders. -/
theorem source_natural_star_row_of_seventeen
    {X K R B : Subgroup G} (h : Input KnownSimple.IsKnownSimple X R B K)
    (h17 : 17 ∣ Nat.card (starImage K R K))
    (hr : primeRank 5 (starImage K R K) = 1) : Nonempty (NaturalStarRow K R) := by
  obtain ⟨hi,⟨c⟩⟩ := star_moved_section_from_source h
  let e := subgroupOfEquivOfLe hi
  obtain ⟨F,⟨a⟩,hq,ho⟩ := ChapterB.SourceInduction.ProjectiveLine.SeventeenRankOne.source_natural _ c
    (by rwa [Nat.card_congr e.toEquiv]) (by rwa [primeRank_congr 5 e])
  exact ⟨⟨hi,c.sectionData,F,a,hq,ho⟩⟩

include j in
/-- The actual exchanged PSL₂(16) factor contradicts the escaping component,
using the complete moved-section classifier on the literal star action. -/
theorem source_exchanged_component_false
    (hfirst : (d.K1.subgroupOf Mc).IsCComponent)
    (hsecond : (d.K2.subgroupOf Mc).IsCComponent)
    (hmodel : Nonempty ((d.K1 ⧸ pCore 2 d.K1) ≃* Theory.PSL2.SixteenWreathComponents.L)) :
    False := by
  have hc := source_component_factors_contained_comparison s d j hfirst hsecond
  have hr : primeRank 5 (starImage j.J (Mc.pCoreIn 2) j.J) = 1 := by
    rw [starImage_five_rank_from_source hc.2.2.2.1,hc.2.1]
  have h17 : 17 ∣ Nat.card (starImage j.J (Mc.pCoreIn 2) j.J) :=
    (by decide : 17 ∣ 4080).trans
      ((source_exchanged_factor_star_intersection_order s d j hfirst hsecond hmodel).trans
        (card_dvd_of_le (starM_le j.J (Mc.pCoreIn 2) (Mc ⊓ normalizer (d.K2 : Set G)))))
  exact hc.2.2.2.2 (source_natural_star_row_of_seventeen hc.2.2.2.1 h17 hr)

/-- Construct and exclude the genuine escaping component in the exchanged
branch. Only the original second-normalizer geometry remains a premise. -/
theorem source_exchanged_geometry_false
    (hfirst : (d.K1.subgroupOf Mc).IsCComponent)
    (hsecond : (d.K2.subgroupOf Mc).IsCComponent)
    (hmodel : Nonempty ((d.K1 ⧸ pCore 2 d.K1) ≃* Theory.PSL2.SixteenWreathComponents.L)) :
    False := by
  obtain ⟨j⟩ := exists_source_escaping_component s d
  exact source_exchanged_component_false s d j hfirst hsecond hmodel

/-- After the exchanged comparison, every surviving source geometry has the
original two residual factors and their actual cyclic-five core quotients. -/
theorem source_normalizer_geometry_residual_models :
    d.K1 = Chapter15.Section03.AbelianAmalgam.GenerationOne.residual H1 ∧
    d.K2 = Chapter15.Section03.AbelianAmalgam.GenerationOne.residual H2 ∧
    Nonempty ((d.K1 ⧸ pCore 2 d.K1) ≃* Multiplicative (ZMod 5)) ∧
    Nonempty ((d.K2 ⧸ pCore 2 d.K2) ≃* Multiplicative (ZMod 5)) := by
  rcases d.models with h | ⟨h1,h2,hm,_⟩
  · exact h
  · exact (source_exchanged_geometry_false s d h1 h2 hm).elim

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
