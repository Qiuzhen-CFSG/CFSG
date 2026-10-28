module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalFieldFour
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalG2CoreNormal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryMaximal

/-!
# Complete G₂ maximality and the unitary field-four sieve in Chapter12

The actual G₂ comparison now gives right maximality at every original
exponent n > 1, including n = 2. The same original normalizer pair therefore
satisfies the local conditions of 5.3, with its maximality, common Sylow and
both enlarged-core premises discharged.

For both ordinary and extended unitary comparisons, the normalizer alternative
is sharpened to a nonnormal original core or an actual A₇/triple-cover quotient
at m = 2, n = 4. No core normality or quotient exclusion is assumed.

The original S, whole overlap, both Cartans and compatible maps are preserved;
original uniqueness remains explicit in Preparation. The outstanding unitary,
Ree and U₅ maximality, exhaustive F.1.12 comparison and ambient completion
recognition are still required for GlobalExit.
Source: Aschbacher–Smith 5.2.8, pp.652–653, and Chapter12, p.795
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Right maximality in the original G₂ row for every n > 1, including field four. -/
theorem rankOne_global_g2_right_maximal_all
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
    residual H ∈ Chapter1.LStar G (T : Subgroup G) :=
  d.g2_right_maximal_all
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F he

/-- The original normalizer pair satisfies the local conditions of 5.3,
with maximality, the common Sylow and both enlarged cores discharged. -/
theorem rankOne_global_g2_normalizer_local_conditions_all
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
      (Global.normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  have hc : Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) := .g2 F he
  exact d.normalizer_local_conditions hi hH (d.g2_right_maximal_all hi hH hp F he) rfl
    (d.common_sylow_of_comparison hi hH.1.1.2 hp hc)
    (d.parabolic_sylow_core_eq_of_comparison hi hH.1.1.2 hp hc)


/-- The literal normalizer-pair application discharges the common Sylow
and enlarged cores and isolates the nonnormal-core or alternating-quotient cases. -/
theorem rankOne_global_unitary_normalizer_or_alternating_obstruction
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (he : (Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (amalgam m hm).reverse)) ∨
      (Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (Extension.amalgam m hm).reverse))) :
    Chapter5.Section03GreenExtension.SourceLocalConditions
      (Global.normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) ∨
      ∃ J ∈ Chapter1.LStar G (T : Subgroup G), residual H < J ∧
        (¬ J ≤ normalizer ((residual H).pCoreIn 2 : Set G) ∨
          m = 2 ∧ n = 4 ∧ J.pCoreIn 2 = (residual H).pCoreIn 2 ∧
            (Chapter1.Section02.LocalModels.IsAlternating (J ⧸ pCore 2 J) 7 ∨
              Chapter1.Section02.LocalModels.IsAlternatingCover (J ⧸ pCore 2 J) 7)) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  rcases d.unitary_maximal_or_alternating_obstruction hi hH hp m hm he with hmax | hh
  · left
    have hc : Global.ConcreteAmalgamComparison
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) :=
      he.elim (.unitary m hm) (.unitaryExtension m hm)
    exact d.normalizer_local_conditions hi hH hmax rfl
      (d.common_sylow_of_comparison hi hH.1.1.2 hp hc)
      (d.parabolic_sylow_core_eq_of_comparison hi hH.1.1.2 hp hc)
  · exact .inr hh


end CFSG.Quasithin.Chapter12.Section02.ChosenModule
