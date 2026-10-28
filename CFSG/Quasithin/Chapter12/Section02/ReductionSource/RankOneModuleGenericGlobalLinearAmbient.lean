module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLinearAmbient.AmbientGeneration

/-!
# The complete prepared maximal-linear Chapter 12 branch

Apply the ambient linear recognizer to the unchanged generic input supplied
by the chosen module. It gives an actual isomorphism of original G with
PSL₃(F), identifies the comparison degree with the original n>1, and supplies
the linear rank-two model in GlobalExit. Field four and both whole-residual
amalgam orientations are retained. No Hall, cubic, generation, order or
recognition premise is added to the original prepared maximal branch.

Source: Aschbacher–Smith F.4.31 and F.4.45–49, printed pp.297–299, and
5.3.2–7, pp.659–661, applied to 12.2 on p.795 of `refs/quasithin.pdf`.
Exhaustive comparison and the nonmaximal branch remain with their assembly
owners; this theorem proves the full prepared maximal-linear branch.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (d : Global.Preparation T L H A B (residual H))
  (hp : Group.IsPerfect (residual H))
  (F : Type) [Field F] [Finite F] [CharP F 2]
  {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
  (he : Nonempty (RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
    (LinearThree.amalgam F)) ∨
    Nonempty (RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
    (LinearThree.amalgam F).reverse))
  (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include D h hmany hn hpsl hH d hp hm hF he hmax


/-- The complete maximal linear branch supplies GlobalExit with its original
exponent, original group carrier and actual PSL₃ witness. -/
theorem rankOne_globalExit_of_linear_comparison : RankOneModule.GlobalExit G := by
  have hpslG := d.linear_ambient_isPSL
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hmax
  exact Or.inl ⟨n,hn,ClassificationModels.IsRankTwoModel.linear (by omega) hpslG⟩

/-- The literal chosen-module input also retains the comparison field and
identifies its degree with the unchanged original n. -/
theorem rankOne_global_linear_ambient_recognition :
    m=n ∧ Nonempty (G ≃* PSL(3,F)) :=
  d.linear_ambient_recognition (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
