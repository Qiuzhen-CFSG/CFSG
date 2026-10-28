module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFour
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalFieldFour

/-!
# The unitary field-four exclusion in the literal Chapter12 pair

The original whole overlap supplies a cubic moving the center of the right
two-core. For a proper maximal overcomponent with normal original core,
the proved core equality and quotient sieve leave A₇ or its triple cover.
The three-rank bound forces the cubic into that perfect overcomponent,
which centralizes its center of order four, a contradiction.

Thus both ordinary and extended unitary comparisons now leave only the
nonnormal-core case of source 5.2.8. The original S, compatible overlap
maps, both Cartans and all core layers are retained; original uniqueness
remains explicit in Preparation. Core normality, remaining maximality rows,
exhaustive comparison and ambient recognition still belong to the assembly.
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

/-- The original normalizer pair satisfies the local conditions of 5.3
unless a maximal overcomponent fails to normalize the original right core.
All normal-core field-four alternatives have been eliminated. -/
theorem rankOne_global_unitary_normalizer_or_nonnormal_core
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
        ¬ J ≤ normalizer ((residual H).pCoreIn 2 : Set G) := by
  exact d.unitary_normalizer_or_nonnormal_core
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
