module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.OrdinaryGeometry.Marking
public import Theory.Representation.BinaryPermutation.SevenParabolic.Span

/-!
# The literal original second-parabolic span in ordinary A₇ coordinates

The original plane marking and the actual second-parabolic image determine
its entire conjugate span: V₀ = ⟨V,e₅₆,e₅₇⟩. Containment in the whole block
module follows from Seven.Setup on the unchanged generated choice.
The source action and parabolic markings remain explicit inputs.
Source: Aschbacher--Smith, original14.6.10(5), printed p.1029.
-/
public section
open Subgroup Theory.GroupTheory BinaryPermutation.SevenParabolic
namespace CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open BinaryPermutation.SevenParabolic.Ordinary
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The chart carries the entire actual plane to the specified binary plane. -/
theorem plane_image (T : Sylow 2 G) (M Mc I H2 : Subgroup G)
    (m : ParabolicMarking T M Mc I H2) : m.chart.image (localModule T M) = plane := by
  ext v
  rw [m.chart.mem_image_lift]
  simpa only [m.chart.coordinate_lift, BinaryPermutation.SevenParabolic.Ordinary.plane] using m.plane (m.chart.lift v)

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- Identify V₀ on the unchanged original source setup, with no span assumption. -/
theorem source_second_span_image
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M))
    (m : ParabolicMarking T M Mc I d.H2) :
    m.chart.image (conjugateSpanBy (localModule T M) (sourceSecondParabolic T I d.H2)) =
      secondSpace := by
  apply m.chart.second_span_image
  · exact (le_conjugateSpanBy _ _).trans
      (generated_span_le_module hG T hempty hM hunique hmany hcard e hab H hH d I hI)
  · exact le_sup_right
  · exact plane_image T M Mc I d.H2 m
  · exact m.second
end CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry
