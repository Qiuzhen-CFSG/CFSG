module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSpecialOddNonfusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSpecialPlacement

/-!
# Odd-degree special-core nonfusion in the chosen-module setup

For the actual G₂ and triality comparisons, the original Sylow/core index
divides the original exponent n. If n is odd, the original T equals S.
This discharges the centralizer-containment premise and yields the marked
short-root involution not fused into the original right-factor center.
The triality calculation retains its cubic-field quotient throughout.

Preparation, including original uniqueness, and the compatible comparison
remain inputs. Even-degree nonfusion and the remaining GlobalExit assembly
are still required. Source: Aschbacher–Smith F.4.29(2,7), pp.289–290,
F.4.35, p.292, and its application in 5.3.3, p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
open _root_.Triality.Standard
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal G₂ nonfusion conclusion, with T=S proved at odd exponent. -/
theorem rankOne_global_g2_short_root_not_fused_of_odd
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (hnOdd : Odd n)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (G2.amalgam (F := F)).reverse)) :
    Global.sourceS L H = (T : Subgroup G) ∧
    let Q := (residual H).pCoreIn 2
    let Z := (center (residual H)).map (residual H).subtype
    ∃ e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (G2.amalgam (F := F)).reverse,
      ∃ v ∈ Q, (∃ w : ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1,
        w.val=v ∧ (e.right w).val=Atlas.G2.rootC (1:F)) ∧
      v ∉ Z ∧ orderOf v=2 ∧ ∀ g : G, v ∉ Z.conjBy g :=
  d.g2_short_root_not_fused_of_odd
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp hnOdd F he


/-- The same source conclusion for the genuine cubic-field triality marking. -/
theorem rankOne_global_triality_short_root_not_fused_of_odd
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1<n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (hnOdd : Odd n) (m : ℕ) (hm : 0<m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (Triality.amalgam (binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (Triality.amalgam (binaryParameters m hm)).reverse)) :
    Global.sourceS L H = (T : Subgroup G) ∧
    let Q := (residual H).pCoreIn 2
    let Z := (center (residual H)).map (residual H).subtype
    ∃ e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (Triality.amalgam (binaryParameters m hm)).reverse,
      ∃ v∈Q, (∃ w : ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1,
        w.val=v ∧ (e.right w).val=RadicalCoordinates.LeviCommutators.short (binaryParameters m hm) rfl 2 1) ∧
      v∉Z ∧ orderOf v=2 ∧ ∀ g : G, v∉Z.conjBy g :=
  d.triality_short_root_not_fused_of_odd
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp hnOdd m hm he


end CFSG.Quasithin.Chapter12.Section02.ChosenModule
