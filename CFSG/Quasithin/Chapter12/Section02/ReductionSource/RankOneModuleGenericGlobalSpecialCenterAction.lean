module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSpecialCenterAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSpecialPlacement

/-!
# The original G₂ and triality center fixers and the left quotient action

The actual compatible G₂ and triality comparisons show that a left Borel element
fixing the right center belongs to the original common Sylow S.
Consequently every original Sylow actor fixing that center acts by an
inner automorphism on L/O₂(L), and lies in S O₂(LT).

This applies the center-action calculation to the literal chosen-module
input. The term O₂(LT) remains explicit; the calculation of the core of
the larger parabolic G₀T does not identify this smaller core. Removing
this term is still needed for the two placements in F.4.35. Original
uniqueness, compatible comparison and completion recognition retain
their producers. Source: Aschbacher–Smith F.4.29(2,7), pp.289–290,
F.4.35, p.292, and 5.3.3, p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- For the original chosen module, fixing the right center forces inner
left quotient action and isolates the remaining intrinsic LT-core. -/
theorem rankOne_global_g2_center_fixer_left_action
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
    let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
    let Z := (center (residual H)).map (residual H).subtype
    (localBorel T L ⊓ centralizer (Z : Set G) ≤ Global.sourceS L H) ∧
    (∀ t : T, t.val ∈ centralizer (Z : Set G) →
      pCoreJoinAction 2 hi.sylow_normalizes (inclusion le_sup_right t) ∈
        MulAut.innerSubgroup (L ⧸ pCore 2 L)) ∧
    (T : Subgroup G) ⊓ centralizer (Z : Set G) ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊔ Global.sourceS L H := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.g2_left_borel_center_kernel hi hH.1.1.2 hp F he,
    d.g2_center_fixer_left_inner hi hH.1.1.2 hp F he,
    d.g2_center_fixer_le_left_core_join_sourceS hi hH.1.1.2 hp F he⟩


/-- The literal chosen-module triality center fixer has inner left quotient
action and lies in S O₂(LT), at every original exponent greater than one. -/
theorem rankOne_global_triality_center_fixer_left_action
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm)).reverse)) :
    let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
    let Z := (center (residual H)).map (residual H).subtype
    (localBorel T L ⊓ centralizer (Z : Set G) ≤ Global.sourceS L H) ∧
    (∀ t : T, t.val ∈ centralizer (Z : Set G) →
      pCoreJoinAction 2 hi.sylow_normalizes (inclusion le_sup_right t) ∈
        MulAut.innerSubgroup (L ⧸ pCore 2 L)) ∧
    (T : Subgroup G) ⊓ centralizer (Z : Set G) ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊔ Global.sourceS L H := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.triality_left_borel_center_kernel hi hH.1.1.2 hp m hm he,
    d.triality_center_fixer_left_inner hi hH.1.1.2 hp m hm he,
    d.triality_center_fixer_le_left_core_join_sourceS hi hH.1.1.2 hp m hm he⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
