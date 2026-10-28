module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeMovedCenter

/-!
# The nonabelian full-core terminal

For a genuinely nonabelian original MS core, the native MS93 distance
alternatives identify the selected order-eight moved factor with the moved
center of the literal full commutator core.  This exports that equality and
its inclusion into the actual core, without replacing the core by a model or
claiming any normalizer invariance.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
open Chapter3.Section02 ChapterC.BinaryMS
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The nonabelian branch has the literal moved-center equality, order eight,
and containment in the center of the actual full MS commutator core. -/
theorem normalizerEscape_nonabelian_core_terminal
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (s : NaturalData D)
    (hout : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      D.maximalLocal)
    (hc : ¬ IsMulCommutative (commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G)))))) :
    let J := L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))
    let A := L.subgroupOf J
    let C := commutatorCore A
    ⁅D.fullModule,L⁆ =
        (⁅Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn C,
          A⁆).map J.subtype ∧
      Nat.card (⁅D.fullModule,L⁆ : Subgroup G) = 8 ∧
      ⁅D.fullModule,L⁆ ≤
        (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn C).map
          J.subtype ∧
      ⁅D.fullModule,L⁆ ≤ C.map J.subtype := by
  have heq := normalizerEscape_moved_center_eq D s hout hc
  have hle := normalizerEscape_moved_le_core_center D (selected_nonnormal s) hout s.quotient
  have hcard : Nat.card (⁅D.fullModule,L⁆ : Subgroup G) = 8 := moved_card s s.fixed_zero
  dsimp only
  exact ⟨heq,hcard,hle,hle.trans (map_mono (map_subtype_le _))⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
