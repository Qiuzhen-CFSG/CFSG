module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryMaximal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFactors

/-!
# The remaining unitary maximality cases for the original Chapter12 pair

For both ordinary and extended unitary comparisons, a proper maximal
local overcomponent that normalizes the original right two-core has
exactly that core. Its actual quotient is in the A.3.14 shortlist, and
the original left exponent is four. Thus the normalizer pair satisfies
the local conditions for 5.3 unless core normality fails or this precise
field-four case occurs. Both cases remain to be excluded by the source
argument; this is not unconditional unitary maximality or GlobalExit.

The actual source S, both Cartans in the whole overlap and both compatible
orientations are retained. The extended overlap core is not identified
with the reduced core. Source: Aschbacher–Smith 5.2.8, pp.652–653 and the
original Chapter12 application, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels.UnitaryFour
open ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The normal-core case of the original unitary comparison forces q = 4
and retains the exact core and actual overcomponent quotient. -/
theorem rankOne_global_unitary_overcomponent_parameter_of_normal
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
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (Extension.amalgam m hm).reverse)))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hKJ : residual H < J)
    (hQ : J ≤ normalizer ((residual H).pCoreIn 2 : Set G)) :
    m = 2 ∧ n = 4 ∧ J.pCoreIn 2 = (residual H).pCoreIn 2 ∧
      AlternatingFive.Shortlist (J ⧸ pCore 2 J) :=
  d.unitary_overcomponent_parameter_of_normal
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he hJ hKJ hQ

/-- No additional maximality or normality premise is inserted: the two
unresolved source cases are displayed as conclusions for the actual pair. -/
theorem rankOne_global_unitary_maximal_or_obstruction
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
    residual H ∈ Chapter1.LStar G (T : Subgroup G) ∨
      ∃ J ∈ Chapter1.LStar G (T : Subgroup G), residual H < J ∧
        (¬ J ≤ normalizer ((residual H).pCoreIn 2 : Set G) ∨
          m = 2 ∧ n = 4 ∧ J.pCoreIn 2 = (residual H).pCoreIn 2 ∧
            AlternatingFive.Shortlist (J ⧸ pCore 2 J)) :=
  d.unitary_maximal_or_obstruction
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he

/-- The literal normalizer-pair application discharges the common Sylow
and enlarged cores and isolates exactly the two remaining unitary cases. -/
theorem rankOne_global_unitary_normalizer_or_obstruction
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
            AlternatingFive.Shortlist (J ⧸ pCore 2 J)) :=
  d.unitary_normalizer_or_obstruction
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
