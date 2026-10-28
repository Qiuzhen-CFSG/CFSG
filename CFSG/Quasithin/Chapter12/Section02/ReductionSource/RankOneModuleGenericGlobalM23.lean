module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalM23.LocalGeneration
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23

/-!
# The actual M23 exit for the nonmaximal linear rank-one branch

Specialize the proved source 5.2.10 recognition theorem using the chosen
module's whole reduced subgroup. The compatible linear comparison and original
whole-residual preparation are retained in either orientation. The conclusion
uses the actual ambient M23 equivalence in GlobalExit.

Source: Aschbacher--Smith 5.2.10 and its Chapter 12 rank-one application.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original nonmaximal linear row gives the actual M23 disjunct. No
recognition, generation or marking-compatibility premise is added. -/
theorem rankOne_globalExit_of_linear_nonmaximal
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (_hgen : 1 < ChapterE.generationParameter H)
    (_hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (_hN : localBorel T L ≤ normalizer (residual H : Set G))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    RankOneModule.GlobalExit G := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  have hequiv := d.linear_nonmaximal_m23_equiv hi hH hp F hm hF he hnonmax
  exact Or.inr (Or.inr hequiv)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
