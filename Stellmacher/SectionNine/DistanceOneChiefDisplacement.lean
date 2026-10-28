module

public import Stellmacher.SectionNine.DistanceOneChiefSubgroup
public import Stellmacher.SectionNine.DistanceOneChiefTerminalProduct
public import Stellmacher.SectionNine.DistanceOneInitialCentralizerKernelData

/-!
# The small displacement in the noncentral initial chief branch

The initial core commutator with the extracted subgroup lies in their
intersection. Modulo the initial center, that intersection has order four.
Consequently the nontrivial commutator image has order at most four, and
the extracted subgroup centralizes that image. These are inputs to the
module recognition in source (9.1)(10), not the chief-index conclusion.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem distance_one_chief_displacement_le_intersection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (branch : DistanceOneChiefBranchData ctx) :
    ⁅q ctx.Γ ctx.criticalPath.a, branch.U⁆ ≤
      branch.U ⊓ q ctx.Γ ctx.criticalPath.a := by
  have hQT := (local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  have hTnormU : T ≤ Subgroup.normalizer branch.U :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer branch.le_sylow).mp
      branch.normal_in_sylow
  have hTnormQ : T ≤ Subgroup.normalizer (q ctx.Γ ctx.criticalPath.a) :=
    (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).1.1.trans
      (stabilizer_le_normalizer_q ctx.Γ ctx.criticalPath.a)
  exact le_inf
    (Subgroup.le_normalizer_iff_commutator_le_right.mp (hQT.trans hTnormU))
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (branch.le_sylow.trans hTnormQ))

public theorem distance_one_chief_intersection_relIndex_four
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (branch : DistanceOneChiefBranchData ctx) :
    (z ctx.Γ ctx.criticalPath.a).relIndex
      (branch.U ⊓ q ctx.Γ ctx.criticalPath.a) = 4 := by
  let Q := q ctx.Γ ctx.criticalPath.a
  let Z := z ctx.Γ ctx.criticalPath.a
  have hZQ : Z ≤ Q :=
    (distance_one_chief_subgroup_properties ctx.toLocalContext).2.1.trans
      (distance_one_chief_subgroup_properties ctx.toLocalContext).1
  have hcount := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G)
    (branch.U ⊓ Z) (branch.U ⊓ Q) bot_le (inf_le_inf_left _ hZQ)
  simp only [Subgroup.relIndex_bot_left] at hcount
  have hinter : (branch.U ⊓ Z).relIndex (branch.U ⊓ Q) =
      Z.relIndex (branch.U ⊓ Q) := by
    rw [← Subgroup.inf_relIndex_right Z (branch.U ⊓ Q)]
    congr 1
    exact ((inf_left_comm Z branch.U Q).trans (by rw [inf_eq_left.mpr hZQ])).symm
  rw [hinter, branch.initial_center_intersection_card,
    branch.initial_core_intersection_card] at hcount
  change Z.relIndex (branch.U ⊓ Q) = 4
  omega

public theorem distance_one_chief_displacement_relIndex_bounds
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (branch : DistanceOneChiefBranchData ctx) :
    1 < (z ctx.Γ ctx.criticalPath.a).relIndex ⁅q ctx.Γ ctx.criticalPath.a, branch.U⁆ ∧
      (z ctx.Γ ctx.criticalPath.a).relIndex ⁅q ctx.Γ ctx.criticalPath.a, branch.U⁆ ≤ 4 := by
  let Z := z ctx.Γ ctx.criticalPath.a
  let D := ⁅q ctx.Γ ctx.criticalPath.a, branch.U⁆
  have hfour := distance_one_chief_intersection_relIndex_four ctx branch
  have hbound := Subgroup.relIndex_le_of_le_right
    (H := Z) (distance_one_chief_displacement_le_intersection ctx branch)
    (by rw [hfour]; decide)
  have hne : Z.relIndex D ≠ 1 := by
    intro heq
    exact branch.noncentral (Subgroup.relIndex_eq_one.mp heq)
  have hpositive : 0 < Z.relIndex D := Nat.pos_of_ne_zero
    (Z.subgroupOf D).index_ne_zero_of_finite
  rw [hfour] at hbound
  change 1 < Z.relIndex D ∧ Z.relIndex D ≤ 4
  exact ⟨by omega, hbound⟩

public theorem distance_one_chief_displacement_quadratic
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (branch : DistanceOneChiefBranchData ctx) :
    ⁅⁅q ctx.Γ ctx.criticalPath.a, branch.U⁆, branch.U⁆ ≤
      z ctx.Γ ctx.criticalPath.a :=
  branch.double_commutator.trans
    (distance_one_terminal_center_le_initial_center ctx.toLocalContext hb)

end Stellmacher.SectionNine
