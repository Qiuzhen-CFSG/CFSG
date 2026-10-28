module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Four
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2Maximal

/-!
# The original G₂(4) cubic actor and the remaining maximality cases

Transport through the compatible whole-overlap map constructs an element
of order three on the actual Chapter12 pair. It centralizes K/O₂(K), acts
fixed-point-freely on O₂(K), and generates that core by commutators.
If a proper maximal overcomponent normalizes the core, this same element
normalizes the overcomponent, whose exact core and A.3.14 quotient are retained.

Thus the normalizer-pair conditions of 5.3 hold unless the field is four
and one of the two displayed maximality cases remains. Core normality and
the field-four representation exclusions are still required. This is not
an exhaustive amalgam comparison or ambient completion recognition.
Source: Aschbacher–Smith 5.2.8, pp.652–653, and the original Chapter12
application, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original pair supplies the cubic actor needed by the small-field
paragraph of 5.2.8; it is in the whole overlap and acts on the actual core. -/
theorem rankOne_global_g2_four_cubic_actor
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^2))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    ∃ x : G, x ∈ ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1 ∧
      orderOf x = 3 ∧ x ∈ normalizer (residual H : Set G) ∧
      (∀ k ∈ residual H, ⁅x,k⁆ ∈ (residual H).pCoreIn 2) ∧
      (∀ q ∈ (residual H).pCoreIn 2, Commute x q → q = 1) ∧
      ⁅(residual H).pCoreIn 2,zpowers x⁆ = (residual H).pCoreIn 2 :=
  d.g2_four_cubic_actor (D.rankOne_generic_input_of_many h hmany (by decide) hpsl)
    hH.1.1.2 hp F he

/-- Both orientations feed the actual normalizer pair. All fields above
four satisfy its local conditions; at four the exact remaining core case
and cubic actor are conclusions, with no extra normalization premise. -/
theorem rankOne_global_g2_normalizer_or_four_obstruction
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    Chapter5.Section03GreenExtension.SourceLocalConditions
      (Global.normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) ∨
      n = 2 ∧ Nat.card F = 4 ∧ ∃ J ∈ Chapter1.LStar G (T : Subgroup G),
        residual H < J ∧
        (¬ J ≤ normalizer ((residual H).pCoreIn 2 : Set G) ∨
          J.pCoreIn 2 = (residual H).pCoreIn 2 ∧
          ChapterA.Section03.SourceEmbeddings.AlternatingFive.Shortlist (J ⧸ pCore 2 J) ∧
          ∃ x : G, x ∈ ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ⊓
              ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1 ∧
            orderOf x = 3 ∧ x ∈ normalizer (J : Set G) ∧
            (∀ k ∈ residual H, ⁅x,k⁆ ∈ (residual H).pCoreIn 2) ∧
            (∀ q ∈ J.pCoreIn 2, Commute x q → q = 1) ∧
            ⁅J.pCoreIn 2,zpowers x⁆ = J.pCoreIn 2) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  rcases d.g2_maximal_or_four_obstruction hi hH hp F he with hmax | hh
  · left
    have hc : Global.ConcreteAmalgamComparison
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) := .g2 F he
    exact d.normalizer_local_conditions hi hH hmax rfl
      (d.common_sylow_of_comparison hi hH.1.1.2 hp hc)
      (d.parabolic_sylow_core_eq_of_comparison hi hH.1.1.2 hp hc)
  · exact .inr hh

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
