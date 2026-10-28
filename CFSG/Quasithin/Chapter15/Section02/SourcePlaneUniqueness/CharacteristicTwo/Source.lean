module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.CubicSymplecticExclusion
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.NoChiBlocks

/-!
# Original 15.2.23 from the preceding source hypotheses

For the actual chosen module and escaping I, suppose F*(I) = O₂(I).
The proved preliminary exclusions remove every chi-block and the NI ≤ MI
branch. The complete component argument then supplies a contradiction on
the same selected component and its full moved section.

The conclusion is the original F*(I) ≠ O₂(I). Its explicit inputs are
only the earlier HStar quotients, Kc orbit alternative, restricted-action
alternative and marked plane inverter, together with PlaneUniquenessPreceding.
Their producers remain with the plane-geometry and small-parabolic owners;
the enclosing plane-uniqueness assembly retains their final discharge.
No local catalogue, module classification, KS placement, small-action
or terminal-exclusion premise remains.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.2.23,
printed pp.1115--1117; refs/quasithin.pdf.
-/

public section
open scoped IsMulCommutative
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
open Section01 ChapterD ChapterD.UniqueFactor
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- Original 15.2.23: an escaping I is not of characteristic two.
Only the earlier quotient, orbit, restricted-action and plane-inverter inputs remain. -/
theorem source_15_2_23
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I)
    (ha : letI := hsource.prepared.elementary;
      Nonempty (internalActionImage M V hsource.prepared.normalized ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (hi : OmegaAction.PlaneInverter hsource ZS) :
    generalizedFitting I ≠ pCore 2 I := by
  intro hfit
  exact ComponentCatalogue.source_component_false d hquotient horbit hI hfit
    (d.no_chi_block horbit hI hfit)
    (d.characteristicTwo_false_of_intersection_le_of_orbit horbit hI hfit) ha hi

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
