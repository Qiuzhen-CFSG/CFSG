module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2CenterKernel
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSpecialCenterAction

/-!
# The original G₂ kernel and marked nonfusion at every field degree

The compatible comparison identifies the actual left-Borel action on the
right quotient. The Borel-normalized actor theorem places O₂(LT) in S,
removing the remaining term from the accepted center-fixer bound. The
original marked root, both compatible maps and the two source placements
then give nonfusion without a parity or centralizer-containment premise.

This is the literal Chapter12 chosen-module application of F.4.35,
printed p.292, used in 5.3.3, p.659 (`refs/quasithin.pdf`). Source uniqueness,
exhaustive comparison and ambient completion recognition remain explicit
in their assembly and are not asserted by this local result.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original core and center-fixer containments, without a parity premise. -/
theorem rankOne_global_g2_center_fixer_control
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
        (G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (G2.amalgam (F := F)).reverse)) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ Global.sourceS L H ∧
      (T : Subgroup G) ⊓ centralizer
        (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G) ≤
          Global.sourceS L H := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.g2_left_core_le_sourceS hi hH.1.1.2 hp F he,
    d.g2_center_fixer_le_sourceS hi hH.1.1.2 hp F he⟩

/-- The marked root remains the image of C(1) under the same right map. -/
theorem rankOne_global_g2_short_root_not_fused
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
        (G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (G2.amalgam (F := F)).reverse)) :
    let Q := (residual H).pCoreIn 2
    let Z := (center (residual H)).map (residual H).subtype
    ∃ e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (G2.amalgam (F := F)).reverse,
      ∃ v ∈ Q, (∃ w : ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1,
        w.val=v ∧ (e.right w).val=Atlas.G2.rootC (1:F)) ∧
      v ∉ Z ∧ orderOf v=2 ∧ ∀ g : G, v ∉ Z.conjBy g :=
  d.g2_short_root_not_fused
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F he


end CFSG.Quasithin.Chapter12.Section02.ChosenModule
