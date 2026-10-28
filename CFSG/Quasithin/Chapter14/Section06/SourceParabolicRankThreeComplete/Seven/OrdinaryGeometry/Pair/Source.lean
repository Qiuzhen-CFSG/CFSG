module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.OrdinaryGeometry.Pair.Geometry.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.OrdinaryGeometry.Pair.Cubic.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.OrdinaryGeometry.Pair.Setup
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.OrdinaryGeometry.Pair.Transport
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.OrdinaryGeometry.Source

/-!
# Assembly of ordinary source-pair recognition

The original H, d and I supply the genuine local configuration. The supplied
chart is relabelled simultaneously; the point fixes the orientation, and the
normalizer description identifies the full M-intersection. The binary-plane
recognition is proved in Geometry.Source, and Cubic.Source recognizes the
two actual cubic subgroup images simultaneously. The final export therefore
has no finite recognition or marking premise.
Source: Aschbacher--Smith, original14.6.10(5), printed p.1029.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation.SevenParabolic
open BinaryPermutation.SevenParabolic.Ordinary
namespace CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

theorem pairInput_of_recognitions (hc : CubicPairRecognition.{u}) (hr : PlaneRecognition) :
    PairInput hG T hempty hM hunique hmany hcard e hab := by
  intro H hH d I hI _ c
  have hd := source_localData hG T hempty hM hunique hmany hcard e hab H hH d I hI
  have hVW := (le_conjugateSpanBy (localModule T M)
      (sourceGeneratedParabolic T M Mc I d.H2)).trans
    (generated_span_le_module hG T hempty hM hunique hmany hcard e hab H hH d I hI)
  obtain ⟨c',hp,hfirst,hsecond,hpoint⟩ := marked_of_recognitions hc hr c hd hVW
  exact ⟨⟨c',hp,hfirst,hsecond,hpoint⟩⟩

/-- The actual geometry consumer, retaining the independent chart constructor. -/
theorem geometryInput_of_chart_and_recognitions
    (chart : ChartInput hG T hempty hM hunique hmany hcard e hab)
    (hc : CubicPairRecognition.{u}) (hr : PlaneRecognition) :
    OrdinaryGeometryInput hG T hempty hM hunique hmany hcard e hab :=
  ordinaryGeometryInput_of_chart_and_pair hG T hempty hM hunique hmany hcard e hab chart
    (pairInput_of_recognitions hG T hempty hM hunique hmany hcard e hab hc hr)

/-- The binary plane and point recognition is discharged; only the simultaneous
classification of the two literal cubic images remains. -/
theorem pairInput_of_cubicRecognition (hc : CubicPairRecognition.{u}) :
    PairInput hG T hempty hM hunique hmany hcard e hab :=
  pairInput_of_recognitions hG T hempty hM hunique hmany hcard e hab hc
    FiniteGeometry.recognition

/-- The original geometry consumer with no finite plane or point premise. -/
theorem geometryInput_of_chart_and_cubicRecognition
    (chart : ChartInput hG T hempty hM hunique hmany hcard e hab)
    (hc : CubicPairRecognition.{u}) :
    OrdinaryGeometryInput hG T hempty hM hunique hmany hcard e hab :=
  ordinaryGeometryInput_of_chart_and_pair hG T hempty hM hunique hmany hcard e hab chart
    (pairInput_of_cubicRecognition hG T hempty hM hunique hmany hcard e hab hc)

/-- The original pair and point acquire compatible partition markings, without
any additional recognition premise. -/
theorem pairInput : PairInput hG T hempty hM hunique hmany hcard e hab :=
  pairInput_of_cubicRecognition hG T hempty hM hunique hmany hcard e hab
    cubicPairRecognition

/-- The actual ordinary geometry consumer with cubic recognition discharged.
Only construction of the explicit whole-module chart remains here. -/
theorem geometryInput_of_chart
    (chart : ChartInput hG T hempty hM hunique hmany hcard e hab) :
    OrdinaryGeometryInput hG T hempty hM hunique hmany hcard e hab :=
  ordinaryGeometryInput_of_chart_and_pair hG T hempty hM hunique hmany hcard e hab chart
    (pairInput hG T hempty hM hunique hmany hcard e hab)

end CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair
