module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityCoreKernel
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSpecialCenterAction

/-!
# Triality core control and marked nonfusion at every field degree

The compatible central torus supplies an order q−1 subgroup of the arms
quotient Borel. Its normalization of the intrinsic LT-core forces that
core's right coefficient to fix the actual base field. The remaining
cubic kernel has odd order and therefore vanishes on this two-group.

These are the literal Chapter12 applications of the core and center-fixer
containments and marked nonfusion in F.4.35, printed p.292, used in 5.3.3,
p.659 (`refs/quasithin.pdf`). Both compatible maps and the original marked
short root are retained. Ambient completion recognition remains separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original core and center-fixer containments, without a parity premise. -/
theorem rankOne_global_triality_center_fixer_control
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm)).reverse)) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ Global.sourceS L H ∧
      (T : Subgroup G) ⊓ centralizer
        (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G) ≤
          Global.sourceS L H := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.triality_left_core_le_sourceS hi hH.1.1.2 hp m hm he,
    d.triality_center_fixer_le_sourceS hi hH.1.1.2 hp m hm he⟩

/-- The same right map retains the original marked short-root involution. -/
theorem rankOne_global_triality_short_root_not_fused
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm)).reverse)) :
    let Q := (residual H).pCoreIn 2
    let Z := (center (residual H)).map (residual H).subtype
    ∃ e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm)).reverse,
      ∃ v ∈ Q, (∃ w : ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1,
        w.val=v ∧ (e.right w).val=_root_.Triality.Standard.RadicalCoordinates.LeviCommutators.short
          (_root_.Triality.Standard.binaryParameters m hm) rfl 2 1) ∧
      v ∉ Z ∧ orderOf v=2 ∧ ∀ g : G, v ∉ Z.conjBy g :=
  d.triality_short_root_not_fused
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he


end CFSG.Quasithin.Chapter12.Section02.ChosenModule
