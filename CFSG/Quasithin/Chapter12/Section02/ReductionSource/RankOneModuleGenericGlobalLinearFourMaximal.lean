module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearFourMaximal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# The L₃(4) right-maximality alternative in the original Chapter12 pair

For the prepared whole-residual pair with original exponent two, an actual
linear-three comparison forces its field to have order four. The right factor
K = O²(H) is either maximal in L(G,T), or lies properly in a maximal exceptional
A₇ block. Both compatible orientations retain S = O₂(N_G(L) ∩ H) and the
whole overlap. No overcomponent classification or module premise is added.

This discharges the L₃(4) branch of source 5.2.8. Preparation still retains
original uniqueness and exhaustive comparison, and the other rows and ambient
completion recognition remain with the generic/global owner. It is not GlobalExit.
Source: Aschbacher–Smith 5.2.8, printed p.652, with the Chapter12 application
on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The full source right-maximality alternative in the linear field-four
row, on the actual residual and its maximal local overcomponent. -/
theorem rankOne_global_linear_four_maximal_or_exceptional
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^2))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (LinearThree.amalgam F).reverse)) :
    m = 2 ∧ (residual H ∈ Chapter1.LStar G (T : Subgroup G) ∨
      ∃ J ∈ Chapter1.LStar G (T : Subgroup G),
        residual H < J ∧ ChapterC.IsExceptionalA7Block J) :=
  d.linear_four_maximal_or_exceptional
    (D.rankOne_generic_input_of_many h hmany (by decide) hpsl) hH hp F hm hF he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
