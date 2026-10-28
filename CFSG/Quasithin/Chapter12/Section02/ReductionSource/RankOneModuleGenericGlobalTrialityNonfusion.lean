module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityNonfusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSpecialPlacement

/-!
# Triality nonfusion in the literal chosen-module setup

The same right-factor marking now supplies movement under the original S
after both source conjugations. Combining this with the centralizing root
pair and special-core saturation proves nonfusion under C_T(Z(K)) ≤ S.
The centralizer premise, original uniqueness and compatible comparison
remain to be discharged; no ambient recognition or GlobalExit is asserted.
Source: Aschbacher–Smith F.4.35, printed p.292, and 5.3.3, p.659.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
open _root_.Triality.Standard
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal chosen-module application retains the original source S,
right-factor marking and whole overlap throughout the nonfusion argument. -/
theorem rankOne_global_triality_short_root_not_fused_of_centralizer_le
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1<n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0<m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (Triality.amalgam (binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (Triality.amalgam (binaryParameters m hm)).reverse))
    (hCS : (T : Subgroup G) ⊓ centralizer
      (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G) ≤ Global.sourceS L H) :
    let Q := (residual H).pCoreIn 2
    let Z := (center (residual H)).map (residual H).subtype
    ∃ e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (Triality.amalgam (binaryParameters m hm)).reverse,
      ∃ v∈Q, (∃ w : ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1,
        w.val=v ∧ (e.right w).val=RadicalCoordinates.LeviCommutators.short (binaryParameters m hm) rfl 2 1) ∧
      v∉Z ∧ orderOf v=2 ∧ ∀ g : G, v∉Z.conjBy g :=
  d.triality_short_root_not_fused_of_centralizer_le
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he hCS

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
