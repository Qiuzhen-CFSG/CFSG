module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.Nonfusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalReeCompletion.Sylow

/-!
# Actual nonconjugate Ree involutions in the original Chapter12 pair

The compatible comparison provides a marked short-root involution with a
perfect linear subgroup in its centralizer. Three divides the order of
that centralizer's solvable residual, whereas the original long-root
centralizer residual is three-free. Thus the two original factors contain
ambient nonconjugate involutions, at every positive parameter including q=8.
Both comparison orientations and the full covering quotients are retained.

This discharges the nonfusion step of F.4.35 on the original prepared pair.
Exhaustion of ambient involutions, full short-root centralizer control,
compatible native normalizer extension and the full-extension order bound
remain before recognition and GlobalExit.
Source: Aschbacher–Smith F.4.35, 5.3.3 and 12.2.2,
printed pp.292,659,795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Actual ambient nonfusion with only the original prepared-row inputs. -/
theorem rankOne_global_ree_involutions_not_fused
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m).reverse)) :
    ∃ z ∈ (center (residual H)).map (residual H).subtype, ∃ v ∈ L,
      orderOf z = 2 ∧ orderOf v = 2 ∧ ¬ IsConj z v := by
  exact d.ree_involutions_not_fused (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp m he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
