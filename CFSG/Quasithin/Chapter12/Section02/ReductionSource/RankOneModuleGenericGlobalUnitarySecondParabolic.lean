module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySecondParabolic
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryLeftCore

/-!
# Closing the unitary right-maximality branch

For the original Chapter12 prepared pair, the nonnormal-core alternative
would give an overcomponent J whose normalizer of U = O₂(L) is both
solvable and nonsolvable. The latter statement now follows from the whole
natural-core action: U is characteristic in O₂(J)U, so its quotient
root-plane parabolic lifts to its literal normalizer in J.

Thus the original right factor is maximal and its normalizer pair satisfies
the source 5.3 local conditions. Both unitary orientations and the degree-two
extension are covered. Original uniqueness remains in Preparation; this
local conclusion does not assert the still-required ambient recognition.
Source: Aschbacher–Smith 5.2.8, printed pp.652–653 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal unitary source pair has maximal right factor and all
normalizer conditions, without an overcomponent or parabolic premise. -/
theorem rankOne_global_unitary_normalizer_local_conditions
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
    residual H ∈ Chapter1.LStar G (T : Subgroup G) ∧
      Chapter5.Section03GreenExtension.SourceLocalConditions
        (Global.normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.unitary_right_maximal hi hH hp m hm he,
    d.unitary_normalizer_local_conditions hi hH hp m hm he⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
