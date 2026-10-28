module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.ModuleSection

/-!
# Algebraic inputs for small-displacement recognition

A finite marked SL3(2) quotient acts nontrivially on an elementary section.
Its kernel acts trivially, and one nonidentity quotient element has
at most two displacement values. These conditions are the input to the
remaining representation theorem; they do not assert its natural model
or its fixed/moving splitting.

The geometric application constructs these inputs from containment of the
transported midpoint span in Q_alpha. Source: Meierfrankenfeld--Stellmacher
(1993), the natural-section inference in (4.6.8), claim (2), p.906.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Generation

/-- A marked binary quotient with nontrivial action and one small displacement.
These are verifiable algebraic hypotheses, not a natural-module conclusion. -/
structure SmallDisplacementData {A : Type*} [Group A]
    (π : A →* SL) (H N : Subgroup A) : Prop where
  projection_surjective : Function.Surjective π
  kernel_le : N ≤ H
  normal_group : H.Normal
  normal_kernel : N.Normal
  elementary : letI := normal_kernel
    IsElementaryAbelian 2 (H ⧸ N.subgroupOf H)
  kernel_action : ⁅H, π.ker⁆ ≤ N
  nontrivial_action : ¬ ⁅H, (⊤ : Subgroup A)⁆ ≤ N
  small_actor : ∃ x : A, π x ≠ 1 ∧ N.relIndex (⁅H, zpowers x⁆) ≤ 2

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Generation
