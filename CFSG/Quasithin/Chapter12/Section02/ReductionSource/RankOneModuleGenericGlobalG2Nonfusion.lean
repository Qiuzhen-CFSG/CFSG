module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Nonfusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSpecialPlacement

/-!
# The marked G₂ nonfusion argument in the chosen-module setup

The actual short-root marking and both source placements now imply nonfusion
under the remaining source centralizer premise C_T(Z(K)) ≤ S. A centralizer
order bound proves movement under the original S after the second conjugation,
so no unproved equality between S and its conjugate is used.

Original uniqueness, the compatible comparison and that Sylow-centralizer
premise still need their source discharge; this does not establish GlobalExit.
Source: Aschbacher–Smith F.4.35, printed p.292, and 5.3.3, p.659.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal chosen-module application constructs the marked short root
and rules out its fusion into the right center, with only C_T(Z(K)) ≤ S
remaining from the Sylow-placement argument. -/
theorem rankOne_global_g2_short_root_not_fused_of_centralizer_le
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
        (G2.amalgam (F := F)).reverse))
    (hCS : (T : Subgroup G) ⊓ centralizer
      (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G) ≤ Global.sourceS L H) :
    let Q := (residual H).pCoreIn 2
    let Z := (center (residual H)).map (residual H).subtype
    ∃ e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (G2.amalgam (F := F)).reverse,
      ∃ v ∈ Q, (∃ w : ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1,
        w.val=v ∧ (e.right w).val=Atlas.G2.rootC (1:F)) ∧
      v ∉ Z ∧ orderOf v=2 ∧ ∀ g : G, v ∉ Z.conjBy g :=
  d.g2_short_root_not_fused_of_centralizer_le
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F he hCS

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
