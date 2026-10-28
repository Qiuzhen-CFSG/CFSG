module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.OrdinaryGeometry.Span
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Source

/-!
# The ordinary A₇ vector from compatible source-pair markings

The first parabolic is contained in the marked M-intersection and hence
fixes the six-support vector. A complementary three-cycle in the actual
second parabolic puts this vector in its actual conjugate span. The image
of its component centralizer is A₆ and has an explicit element outside both
marked intersections. This supplies every field of OrdinaryGeometry.

The remaining inputs concern whole-module coordinates and recognition of
the original parabolic pair. They are not assumed fixed-vector or escape
conclusions. The final source theorem still awaits their construction.
Source: Aschbacher--Smith, original14.6.10(5), printed pp.1029--1030.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation.SevenParabolic
namespace CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open BinaryPermutation.SevenParabolic.Ordinary
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The unchanged original d and I acquire the required geometric witness
from an action marking, by the literal module and centralizer calculations. -/
theorem geometry_of_marking (T : Sylow 2 G) (M Mc I H2 : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (m : ParabolicMarking T M Mc I H2) :
    Nonempty (Seven.OrdinaryGeometry T M Mc I H2) := by
  let J := sourceGeneratedParabolic T M Mc I H2
  let C := sourceGeneratedComponent T M Mc I H2
  let c := m.chart
  have hf : ((J ⊓ M).subgroupOf J).map c.actor ≤ lambda := by
    change ((J ⊓ M).subgroupOf J).map m.chart.actor ≤ lambda
    rw [m.first]
    exact inf_le_right
  have hz : (c.lift firstFour : G) ∈ localModule T M := by
    apply (m.plane _).mpr
    rw [c.coordinate_lift]
    exact Submodule.subset_span (Set.mem_insert _ _)
  have hw : (c.lift secondFour : G) ∈ localModule T M := by
    apply (m.plane _).mpr
    rw [c.coordinate_lift]
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hcycle : complementCycle ∈
      ((sourceSecondParabolic T I H2).subgroupOf J).map c.actor := by
    rw [m.second]
    refine ⟨?_,complementCycle_mem.1⟩
    have ha : complementCycle ∈ (C.subgroupOf J).map c.actor :=
      c.component_image ▸ complementCycle_mem.2
    exact map_le_range _ _ ha
  have hfixed := c.sixSupport_fixed (J ⊓ M) inf_le_left hf
  have hR : firstResidual T M Mc I H2 ≤ J ⊓ M :=
    le_inf ((map_subtype_le _).trans inf_le_right)
      (((map_subtype_le _).trans inf_le_left).trans (sourceResidual_le M Mc))
  have hS : (T : Subgroup G) ⊓ J ≤ J ⊓ M := le_inf inf_le_right (inf_le_left.trans hTM)
  obtain ⟨hM,hMc⟩ := c.sixSupport_escapes M Mc hf m.point
  exact ⟨{
    vector := c.lift firstSix
    mem_span := c.sixSupport_mem_span (localModule T M) (sourceSecondParabolic T I H2) hz hw hcycle
    ne_one := c.lift_ne_one firstSix_ne_zero
    first_fixed := hR.trans hfixed
    sylow_fixed := hS.trans hfixed
    escapes_M := hM
    escapes_Mc := hMc }⟩

omit [Finite G] in
/-- The original second image is strictly smaller than the image of the
point stabilizer. This remains true in both possible A₇/S₇ extensions. -/
theorem second_image_lt_point (T : Sylow 2 G) (M Mc I H2 : Subgroup G)
    (m : ParabolicMarking T M Mc I H2) :
    ((sourceSecondParabolic T I H2).subgroupOf
      (sourceGeneratedParabolic T M Mc I H2)).map m.chart.actor <
      m.chart.actor.range ⊓ pointStabilizer firstFour := by
  rw [m.second]
  apply theta_lt_point
  rw [←m.chart.component_image]
  exact map_le_range _ _

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- Discharge the exact public geometry contract from the source pair marking. -/
theorem ordinaryGeometryInput_of_marking
    (hm : MarkingInput hG T hempty hM hunique hmany hcard e hab) :
    OrdinaryGeometryInput hG T hempty hM hunique hmany hcard e hab := by
  intro H hH d I hI hb
  obtain ⟨m⟩ := hm H hH d I hI hb
  exact geometry_of_marking T M Mc I d.H2 hM.1.2 m

/-- Assemble the independently constructed action chart and pair recognition. -/
theorem ordinaryGeometryInput_of_chart_and_pair
    (hc : ChartInput hG T hempty hM hunique hmany hcard e hab)
    (hp : PairInput hG T hempty hM hunique hmany hcard e hab) :
    OrdinaryGeometryInput hG T hempty hM hunique hmany hcard e hab := by
  apply ordinaryGeometryInput_of_marking hG T hempty hM hunique hmany hcard e hab
  intro H hH d I hI hb
  obtain ⟨c⟩ := hc H hH d I hI hb
  exact hp H hH d I hI hb c

/-- Actual Seven.Source consumer: the ordinary geometry premise is discharged;
whole-block reconstruction, exceptional rank and both source producers remain explicit. -/
theorem source_branch_of_chart_and_pair
    (hc : ChartInput hG T hempty hM hunique hmany hcard e hab)
    (hp : PairInput hG T hempty hM hunique hmany hcard e hab)
    (hr : ReconstructionInput hG T hempty hM hunique hmany hcard e hab)
    (hx : ExceptionalRankInput hG T hempty hM hunique hmany hcard e hab) :
    SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
      (fun C => Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 7))) :=
  source_branch_of_inputs hG T hempty hM hunique hmany hcard e hab hr
    (ordinaryGeometryInput_of_chart_and_pair hG T hempty hM hunique hmany hcard e hab hc hp) hx
end CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry
