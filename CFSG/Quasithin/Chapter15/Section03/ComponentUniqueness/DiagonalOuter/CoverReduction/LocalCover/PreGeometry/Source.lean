module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.PreGeometry.CenterReduction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.PreGeometry.ProjectiveRoots
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.PreGeometry.CentralLift

/-!
# The source geometry before the component-kernel argument

The actual Borel construction selects compatible labels for the two original
planes. Its moving root forces the field order to be four. The complete
15.3.7 alternatives then give E₉, and quotient-action image generation supplies
an outer cubic actor in the opposite full plane residual.

The proved projective root calculations and central-kernel lifting now identify
the component centre and both local centralizers with the first chosen plane.
Every intrinsic calculation is discharged, in the original quotient marking.
Neither the full 15.3.37 product nor arbitrary-automorphism coverage is an input.
The earlier conclusions remain uniform over eligible outside overgroups, so
this construction can be applied again when the source enlarges the overgroup.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of 15.3.38,
printed pp.1135--1136, using the earlier conclusions 15.3.2--12/25/33/36.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
open Candidates.LinearCore
variable {G : Type*} [Group G] [Finite G]

/-- Constructed output of the first centre reduction. The inherited data retain
the original marking, compatible plane interchange, E₉ quotient and both full
residuals. These fields are conclusions of `precentre_of_marked_source`. -/
structure PrecentreData (d : CharacteristicTwo.LocalData G) (I L : Subgroup G)
    {n : ℕ} (c : ProjectiveMarking L (2 ^ n)) (y : d.Yplus)
    extends PreparedResiduals d I L c y where
  center_core : center L = pCore 2 L
  center_plane : centerImage L = borel.W₁
  sylow_centralizer : d.S ⊓ centralizer (L : Set G) = borel.W₁
  overgroup_centralizer : I ⊓ centralizer (L : Set G) = borel.W₁
  opposite_core : (planeResidual d.M d.Y borel.W₂).pCoreIn 2 = d.S ⊓ L
  residual_core : d.Y.pCoreIn 2 = d.S ⊓ L
  residual_product : (d.Y : Set G) = (componentPart d.Yplus L : Set G) *
    (planeResidual d.M d.Y borel.W₂ : Set G)

/-- Discharge both intrinsic producers before applying the centre reduction. -/
theorem precentreData_of_prepared
    {d : CharacteristicTwo.LocalData G} {I L : Subgroup G} {n : ℕ}
    {c : ProjectiveMarking L (2 ^ n)} {y : d.Yplus}
    (g : PreparedResiduals d I L c y) (h : MatrixImage.SourceSetup d I L)
    (hΩ : centralOmegaIn d.S ≤ d.V)
    (hVY : d.V ⊓ centralizer (d.Y : Set G) = ⊥) :
    Nonempty (PrecentreData d I L c y) := by
  obtain ⟨r⟩ := projectiveRootData_of_prepared c y h g
  have m := precentreCalculations_of_projectiveRootData g h hΩ hVY r
  obtain ⟨hc, hz, hs, hi, hd, hq, hp⟩ := precentre_of_prepared_residuals g h hΩ hVY m
  exact ⟨{ toPreparedResiduals := g
           center_core := hc
           center_plane := hz
           sylow_centralizer := hs
           overgroup_centralizer := hi
           opposite_core := hd
           residual_core := hq
           residual_product := hp }⟩

/-- The earlier source reduction in the supplied marking. All Borel, plane,
root and cover calculations are proved; the premises are the selected marked
branch and exact earlier local conclusions. In particular no centre identity,
`RankTwoDiagonal`, or product with the original actor is assumed. -/
theorem precentre_of_marked_source
    {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (h : MatrixImage.SourceSetup d I L) (e : SourceBorel.Earlier d)
    {n : ℕ} (hn : 0 < n) (heven : Even n) (c : ProjectiveMarking L (2 ^ n))
    (y : d.Yplus) (hy : c.Diagonal (y : G))
    (hcase : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ d.S) d.M →
      d.Yplus = Stellmacher.twoResidualAmbient (d.Y ⊓ centralizer (d.V₁ : Set G)) →
      normalizer (d.V₁ : Set G) ≤ d.M ∧ normalizer (d.V₂ : Set G) ≤ d.M)
    (h7 : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
      ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action)
    (himage7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hΩ : centralOmegaIn d.S ≤ d.V)
    (hVY : d.V ⊓ centralizer (d.Y : Set G) = ⊥) :
    Nonempty (PrecentreData d I L c y) := by
  obtain ⟨g⟩ := preparedResiduals_of_marked_source h e hn heven c y hy hcase h7 himage7
  exact precentreData_of_prepared g h hΩ hVY

/-- Centre control for the earlier component-kernel consumer, stated without
choosing a plane label in the conclusion. The compatible orientation is
constructed internally; no full product or centre certificate is an input. -/
theorem center_control_of_marked_source
    {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    (h : MatrixImage.SourceSetup d I L) (e : SourceBorel.Earlier d)
    {n : ℕ} (hn : 0 < n) (heven : Even n) (c : ProjectiveMarking L (2 ^ n))
    (y : d.Yplus) (hy : c.Diagonal (y : G))
    (hcase : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ d.S) d.M →
      d.Yplus = Stellmacher.twoResidualAmbient (d.Y ⊓ centralizer (d.V₁ : Set G)) →
      normalizer (d.V₁ : Set G) ≤ d.M ∧ normalizer (d.V₂ : Set G) ≤ d.M)
    (h7 : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
      ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action)
    (himage7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hΩ : centralOmegaIn d.S ≤ d.V)
    (hVY : d.V ⊓ centralizer (d.Y : Set G) = ⊥) :
    n = 2 ∧ center L = pCore 2 L ∧
      d.S ⊓ centralizer (L : Set G) = centerImage L ∧
      I ⊓ centralizer (L : Set G) = centerImage L := by
  obtain ⟨g⟩ := precentre_of_marked_source h e hn heven c y hy hcase h7 himage7 hΩ hVY
  exact ⟨g.parameter, g.center_core, g.sylow_centralizer.trans g.center_plane.symm,
    g.overgroup_centralizer.trans g.center_plane.symm⟩

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
