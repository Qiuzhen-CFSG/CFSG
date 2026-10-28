module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2CoreNormal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2Four

/-!
# Core normality in the original G₂ pair, including field four

For every maximal local overcomponent J of K = O²(H), the original
whole-overlap comparison gives O₂(J) = O₂(K) and normalization of J by
N_G(K). The central omega argument in the source extension proves this
without a core-normality premise. It uses the literal chosen-module pair.

Consequently the earlier normalizer alternative loses its nonnormal-core
branch. A proper overcomponent can occur only at n = 2 and field order
four, with the actual A.3.14 quotient shortlist and the same original
cubic actor. Excluding that remaining configuration, the unitary/Ree/U₅
maximality arguments, exhaustive comparison and ambient recognition remain
required. Original uniqueness remains explicit in Preparation.

Source: Aschbacher–Smith 5.2.8, printed pp.652–653, and its Chapter12
application on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal maximal overcomponent has the original core at every
allowed exponent, and the whole original normalizer preserves it. -/
theorem rankOne_global_g2_maximal_overcomponent_core
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
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hKJ : residual H ≤ J) : J.pCoreIn 2 = (residual H).pCoreIn 2 ∧
      normalizer (residual H : Set G) ≤ normalizer (J : Set G) :=
  d.g2_maximal_overcomponent_core
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F he hJ hKJ

/-- Both compatible orientations now give the normalizer conditions or
only the field-four quotient configuration. Core normality and the cubic
actor's normalization of J are discharged. -/
theorem rankOne_global_g2_normalizer_or_four_shortlist
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
        J.pCoreIn 2 = (residual H).pCoreIn 2 ∧
          ChapterA.Section03.SourceEmbeddings.AlternatingFive.Shortlist (J ⧸ pCore 2 J) ∧
          ∃ x : G, x ∈ ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ⊓
              ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1 ∧
            orderOf x = 3 ∧ x ∈ normalizer (J : Set G) ∧
            (∀ k ∈ residual H, ⁅x,k⁆ ∈ (residual H).pCoreIn 2) ∧
            (∀ q ∈ J.pCoreIn 2, Commute x q → q = 1) ∧
            ⁅J.pCoreIn 2,zpowers x⁆ = J.pCoreIn 2 := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  rcases d.g2_maximal_or_four_shortlist hi hH hp F he with hmax | hh
  · left
    have hc : Global.ConcreteAmalgamComparison
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) := .g2 F he
    exact d.normalizer_local_conditions hi hH hmax rfl
      (d.common_sylow_of_comparison hi hH.1.1.2 hp hc)
      (d.parabolic_sylow_core_eq_of_comparison hi hH.1.1.2 hp hc)
  · exact .inr hh

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
