module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesConstituent
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesQuadraticResidual
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesOrbitCore

/-!
# The original homogeneous orbit has a faithful SQTK actor with residual F*

The homogeneous section already selected in the centralizer-span action is
retained. Its central quotient has kernel exactly the two-core of the
residual--Sylow join. The original quotient projection identifies the
generalized Fitting subgroup of its faithful actor with PSL₃(4), and the
residual's odd-prime rank bounds give SQTK for that actor. The existing
diagram obstruction applies on this same central quotient.

This removes the generalized-Fitting and SQTK premises from the subsequent
D.3/B.4 application. Middle-layer fixedness, the Suzuki branch and the
orbit-collapse argument remain open; neither the abelian-span theorem nor
irreducibility of this orbit is asserted here. Final source assembly remains
qt-d-1222-linear-field-cubic-escape.
Source: Aschbacher--Smith 5.1.23, printed pp.645--646, `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H C : Subgroup G} {z : G}

/-- Any homogeneous seed on the original residual action has the required
kernel, generalized Fitting subgroup, actual PSL₃(4) model and SQTK actor. -/
theorem linear_cubic_residual_orbit_structure
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (d : CubicEscape.LocalData T H C z) :
    let s := linear_cubic_centralizer_setup h d
    let K := ((residual H).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
    let P := ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
    SpanAction.ResidualOrbitStructure KnownSimple.IsKnownSimple
      (SpanAction.representation s) K P := by
  let s := linear_cubic_centralizer_setup h d
  obtain ⟨hn,hm⟩ := linear_cubic_residual_image h hH hK hnf hlinear d
  let := hn
  have hP := T.isPGroup'.comap_subtype.map (SpanAction.projection s)
  have ht : orderOf z = 2 := by simpa only [Nat.card_zpowers] using d.point_card
  have hkg : IsKGroup KnownSimple.IsKnownSimple (SpanAction.Actor s) :=
    (h.simpleQTKE.involution_centralizer_sqtk ht).isKGroup.of_surjective
      (SpanAction.projection s) (SpanAction.projection_surjective s)
  exact SpanAction.residual_orbit_structure_all (SpanAction.representation s) _ _ hm hP
    KnownSimple.IsKnownSimple (linear_cubic_residual_image_sqtk h hH hK hnf d) hkg

/-- The previously constructed orbit section supplies all structural inputs;
the seed is chosen once and the original diagram obstruction is retained. -/
theorem linear_cubic_residual_orbit_fitting_section
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (d : CubicEscape.LocalData T H C z) :
    let s := linear_cubic_centralizer_setup h d
    let K := ((residual H).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
    let P := ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
    SpanAction.HasResidualOrbitFittingSection KnownSimple.IsKnownSimple
      (SpanAction.representation s) K P ∧
      NoHermitianCentralSections (SpanAction.representation s) K P := by
  refine ⟨?_,linear_cubic_central_section_no_hermitian_coordinates D h hH hK hnf hlinear d⟩
  exact SpanAction.residual_orbit_fitting_section KnownSimple.IsKnownSimple _ _ _
    (linear_cubic_residual_orbit_section h hH hK hnf hlinear d)
    (linear_cubic_residual_orbit_structure h hH hK hnf hlinear d)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
