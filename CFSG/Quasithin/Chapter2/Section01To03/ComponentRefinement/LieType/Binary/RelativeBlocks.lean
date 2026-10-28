module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Setup
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Blocks
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.BlockObstructions
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.Geometry
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.Projection
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.CentralizerGeometry
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.RelativeBlocks.FlagGeometry
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.RelativeBlocks.EndNodes
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.RelativeBlocks.MiddleFlag

/-!
# Relative blocks in binary flag overgroups

The `{1,4}` flag in degree five is identified geometrically with the
centralizer flag of the projected transvection. Its entire overgroup lies
in M, so every relative block lies in M as well.

Every end-node block has the natural binary type of dimension three or four,
with its actual quotient and conjugation module identified by the end-node
calculation. The separate degree-five `{2,3}` calculation excludes every
short subnormal block of that overgroup. These two results discharge the
premises of the preserved conditional reduction and establish the relative
block obstruction for every excluded flag shape. Transvection coordinates
remain an explicit geometric input; final component elimination belongs to
the parent binary assembly.

All blocks are subnormal in the displayed flag overgroup. Neither the
whole parabolic nor its two-residual is declared to be a block.

Source: Aschbacher–Smith 2.3.9(7), printed pp.525–526, with the genuine
short-group, block and χ₀ definitions C.1.7 and C.1.12, printed pp.123–124.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open Subgroup ChapterC

variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
  {n : ℕ} [NeZero n] {e : L ≃* PSL n} {t : L}

/-- The centralizer-flag case accounts for every subgroup of the local overgroup,
and therefore for every moved χ₀ block, with its original relative subnormality. -/
theorem blockObstruction_of_centralizer_flag
    (h : LocalSetup H L M S z) (ht : IsConjugationProjection L z t)
    (c : TransvectionCoordinates e t) (F : Flag n) (hn : 2 ≤ n)
    (hSF : ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F)
    (hF : F.types = {1, n - 1}) :
    BlockObstruction M ((S : Subgroup H).map H.subtype)
      (flagOvergroup e F ((S : Subgroup H).map H.subtype)) := by
  intro B _ _
  exact (map_subtype_le B).trans (c.flagOvergroup_le_of_types h ht F hn hSF hF)

/-- Assembly of the excluded shapes, conditional only on the two remaining
relative-block calculations. The `{1,4}` case is discharged by geometry. -/
theorem blockObstruction_of_flag_calculations
    (h : LocalSetup H L M S z) (ht : IsConjugationProjection L z t)
    (c : TransvectionCoordinates e t) (F : Flag n) (hF : ExcludedFlagShape F)
    (hSF : ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F)
    (hEnd : F.types = {1} ∨ F.types = {n - 1} →
      ∀ B : Subgroup (flagOvergroup e F ((S : Subgroup H).map H.subtype)),
        IsBlock B →
        B.map (flagOvergroup e F ((S : Subgroup H).map H.subtype)).subtype =
          ⁅B.map (flagOvergroup e F ((S : Subgroup H).map H.subtype)).subtype,
            Stellmacher.elementaryAbelianMaxJ ((S : Subgroup H).map H.subtype)⁆ →
        ¬ B.map (flagOvergroup e F ((S : Subgroup H).map H.subtype)).subtype ≤ M →
        IsLinearTwoBlock B 3 ∨ IsLinearTwoBlock B 4)
    (hMiddle : n = 5 → F.types = {2, 3} →
      ∀ B : Subgroup (flagOvergroup e F ((S : Subgroup H).map H.subtype)),
        IsBlock B →
        B.map (flagOvergroup e F ((S : Subgroup H).map H.subtype)).subtype =
          ⁅B.map (flagOvergroup e F ((S : Subgroup H).map H.subtype)).subtype,
            Stellmacher.elementaryAbelianMaxJ ((S : Subgroup H).map H.subtype)⁆ →
        ¬ B.map (flagOvergroup e F ((S : Subgroup H).map H.subtype)).subtype ≤ M →
        False) :
    BlockObstruction M ((S : Subgroup H).map H.subtype)
      (flagOvergroup e F ((S : Subgroup H).map H.subtype)) := by
  rcases hF with ⟨rfl, hF⟩ | ⟨rfl, hF⟩
  · exact blockObstruction_of_binary_natural (hEnd hF)
  · rcases hF with hF | hF | hF | hF
    · exact blockObstruction_of_binary_natural (hEnd (Or.inl hF))
    · exact blockObstruction_of_binary_natural (hEnd (Or.inr hF))
    · exact blockObstruction_of_centralizer_flag h ht c F (by decide) hSF hF
    · apply blockObstruction_of_binary_natural
      intro B hB hm hout
      exact (hMiddle rfl hF B hB hm hout).elim

/-- The complete relative block calculation for the excluded binary flags.
The end-node quotient/module calculation and the middle-flag shortness
exclusion discharge both premises of `blockObstruction_of_flag_calculations`.
The degree-five `{1,4}` flag is identified with the centralizer flag there.

This applies in particular to the source's `HeOver(S)` overgroups and
order-two projection; neither extra assumption is needed once the displayed
coordinates, flag invariance and Sylow containment are supplied. Subnormality
is always relative to the full-S flag overgroup. -/
theorem blockObstruction_of_excluded_flag
    (h : LocalSetup H L M S z) (ht : IsConjugationProjection L z t)
    (c : TransvectionCoordinates e t) (F : Flag n) (hF : ExcludedFlagShape F)
    (hinv : FlagInvariant e ((S : Subgroup H).map H.subtype) F)
    (hSF : ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F) :
    BlockObstruction M ((S : Subgroup H).map H.subtype)
      (flagOvergroup e F ((S : Subgroup H).map H.subtype)) := by
  apply blockObstruction_of_flag_calculations h ht c F hF hSF
  · intro hEnd B hB _ _
    have hn : n = 4 ∨ n = 5 :=
      hF.elim (fun hf => Or.inl hf.1) (fun hf => Or.inr hf.1)
    exact endNode_block_types h hn e ht c F hEnd hinv hSF B hB
  · rintro rfl hMiddle B hB _ _
    exact not_isBlock_of_middle_flag h e F hMiddle hinv B hB

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary

end
