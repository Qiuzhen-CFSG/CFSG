module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveMaximal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionUnitaryFive

/-!
# Right maximality of the special U₅(4) pair

The surviving U₅(4) comparison identifies the original right residual's
quotient with SU₃(4). The non-enlargement theorem for that actual section
makes the right residual maximal in L(G,T). The common Sylow and enlarged
core identities then give the literal normalizer conditions of 5.3.

The comparison retains both endpoint maps and the original whole overlap.
Original uniqueness remains in Preparation. Exhaustive amalgam comparison
and ambient recognition are still required for the global exit.
Source: Aschbacher–Smith 5.2.8, printed p.652, using 1.2.8(4), and the
Chapter12 application on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original U₅(4) right residual is maximal and its normalizer pair
satisfies the source local conditions, with those premises discharged. -/
theorem rankOne_global_unitaryFive_normalizer_local_conditions
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (M : Model 4)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) M.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) M.amalgam.reverse)) :
    residual H ∈ Chapter1.LStar G (T : Subgroup G) ∧
      Chapter5.Section03GreenExtension.SourceLocalConditions
        (Global.normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.unitaryFive_right_maximal hi hH hp M he,
    d.unitaryFive_normalizer_local_conditions hi hH hp M he⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
