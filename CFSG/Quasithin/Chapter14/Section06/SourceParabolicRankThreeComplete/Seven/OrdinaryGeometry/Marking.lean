module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Setup
public import Theory.Representation.BinaryPermutation.SevenParabolic.Conjugation

/-!
# Compatible ordinary coordinates for the original generated parabolics

The marking records the action and the original plane and intersections.
It contains neither the six-support vector nor any fixed-vector or escape
conclusion. Its construction is the outstanding source-pair recognition
step; the coordinate calculation constructs OrdinaryGeometry from it.

Source: Aschbacher--Smith, original14.6.10(5), printed p.1029.
-/

@[expose] public section
open Subgroup Theory.GroupTheory BinaryPermutation.SevenParabolic
namespace CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open BinaryPermutation.SevenParabolic.Ordinary
variable {G : Type*} [Group G] [Finite G]

/-- All coordinates refer to the unchanged generated group and its literal block module. -/
structure ParabolicMarking (T : Sylow 2 G) (M Mc I H2 : Subgroup G) where
  chart : Chart (sourceGeneratedParabolic T M Mc I H2)
    (sourceGeneratedComponent T M Mc I H2)
    ((ChapterC.blockU (sourceGeneratedComponent T M Mc I H2)).map
      (sourceGeneratedComponent T M Mc I H2).subtype)
  plane : ∀ w : (ChapterC.blockU (sourceGeneratedComponent T M Mc I H2)).map
      (sourceGeneratedComponent T M Mc I H2).subtype,
    (w : G) ∈ localModule T M ↔
      (chart.moduleEquiv w).toAdd ∈ Submodule.span (ZMod 2) {firstFour,secondFour}
  first : (((sourceGeneratedParabolic T M Mc I H2 ⊓ M).subgroupOf
      (sourceGeneratedParabolic T M Mc I H2)).map chart.actor) = chart.actor.range ⊓ lambda
  second : ((sourceSecondParabolic T I H2).subgroupOf
      (sourceGeneratedParabolic T M Mc I H2)).map chart.actor = chart.actor.range ⊓ theta
  point : (((sourceGeneratedParabolic T M Mc I H2 ⊓ Mc).subgroupOf
      (sourceGeneratedParabolic T M Mc I H2)).map chart.actor) ≤ pointStabilizer firstFour

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- Whole-module coordinates on the actual generated component, before a choice of labels. -/
def ChartInput : Prop :=
  ∀ (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G),
    I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M) →
    ChapterC.IsAlternatingBlock (sourceGeneratedComponent T M Mc I d.H2) 7 →
      Nonempty (Chart (sourceGeneratedParabolic T M Mc I d.H2)
        (sourceGeneratedComponent T M Mc I d.H2)
        ((ChapterC.blockU (sourceGeneratedComponent T M Mc I d.H2)).map
          (sourceGeneratedComponent T M Mc I d.H2).subtype))

/-- Source-pair recognition, separate from the subsequent vector calculation. -/
def MarkingInput : Prop :=
  ∀ (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G),
    I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M) →
    ChapterC.IsAlternatingBlock (sourceGeneratedComponent T M Mc I d.H2) 7 →
      Nonempty (ParabolicMarking T M Mc I d.H2)
/-- Recognition of the original pair may start from an arbitrary compatible
chart and relabel it. It must prove the point and both partition markings. -/
def PairInput : Prop :=
  ∀ (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G),
    I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M) →
    ChapterC.IsAlternatingBlock (sourceGeneratedComponent T M Mc I d.H2) 7 →
    Chart (sourceGeneratedParabolic T M Mc I d.H2)
      (sourceGeneratedComponent T M Mc I d.H2)
      ((ChapterC.blockU (sourceGeneratedComponent T M Mc I d.H2)).map
        (sourceGeneratedComponent T M Mc I d.H2).subtype) →
    Nonempty (ParabolicMarking T M Mc I d.H2)
end CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry
