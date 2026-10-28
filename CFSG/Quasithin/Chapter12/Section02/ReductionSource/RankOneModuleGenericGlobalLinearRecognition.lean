module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLinearAmbient
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalM23

/-!
# The full prepared linear alternative in Chapter 12

Split on maximality of the original whole residual. The completed maximal
recognizer identifies G with PSL₃ over the comparison field at the original
exponent n > 1. The completed nonmaximal recognizer identifies G with the
actual M₂₃ carrier. Thus either orientation of the original linear comparison
gives GlobalExit without a maximality assumption or any further recognition
input. Field four, both full endpoint maps, and their whole overlap are retained.

Source: Aschbacher--Smith 5.2.8--10, printed pp.651--653, and 5.3.4--7,
printed pp.659--661, applied in Chapter 12 on p.795 (`refs/quasithin.pdf`).
Exhaustive selected-factor comparison and the other ambient rows remain
separate obligations of the generic/global assembly.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The two completed source branches identify original G with an actual
PSL₃ or M₂₃ carrier, without assuming maximality of the whole residual. -/
theorem rankOne_global_linear_or_m23_recognition
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
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
    (m = n ∧ 1 < m ∧ ClassicalGroup.IsPSL G 3 (2^n) ∧ Nonempty (G ≃* PSL(3,F))) ∨
      Nonempty (G ≃* Sporadic.Mathieu.M23) := by
  classical
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  by_cases hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G)
  · exact Or.inl (d.linear_ambient_recognition_full hi hH hp F hm hF he hmax)
  · exact Or.inr (d.linear_nonmaximal_m23_equiv hi hH hp F hm hF he hmax)

/-- The entire linear-amalgam branch gives the original strict GlobalExit;
the original maximal and nonmaximal residual cases are both discharged. -/
theorem rankOne_globalExit_of_linear_amalgam
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
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
    RankOneModule.GlobalExit G := by
  rcases D.rankOne_global_linear_or_m23_recognition h hmany hn hpsl hH d hp F hm hF he with
    hlinear | hmathieu
  · exact Or.inl ⟨n,hn,ClassificationModels.IsRankTwoModel.linear (by omega) hlinear.2.2.1⟩
  · exact Or.inr (Or.inr hmathieu)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
