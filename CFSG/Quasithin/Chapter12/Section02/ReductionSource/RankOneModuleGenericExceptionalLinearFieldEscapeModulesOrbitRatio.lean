module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesOrbitCore
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesOrbitRatio

/-!
# The original orbit quotient has no quadratic offender of ratio at most two

For every homogeneous seed of the literal residual action, the previously
constructed central quotient has quadratic ratio greater than two and cubic
ratio greater than one. The original involution centralizer supplies the
K-group hypothesis and the literal residual supplies SQTK. No orbit
irreducibility or additional module hypothesis is imposed.

The same constructed orbit retains its generalized-Fitting calculation and
the original diagram obstruction. These are inputs to the remaining cubic
orbit-collapse step; they do not prove abelianness of the centralizer span.
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

/-- Intrinsic ratio bounds on every previously selected residual orbit quotient. -/
theorem linear_cubic_residual_orbit_ratios
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (d : CubicEscape.LocalData T H C z) :
    let s := linear_cubic_centralizer_setup h d
    let K := ((residual H).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
    let P := ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
    SpanAction.ResidualOrbitRatios (SpanAction.representation s) K P := by
  let s := linear_cubic_centralizer_setup h d
  obtain ⟨hn,hm⟩ := linear_cubic_residual_image h hH hK hnf hlinear d
  let := hn
  have ht : orderOf z = 2 := by simpa only [Nat.card_zpowers] using d.point_card
  have hkg : IsKGroup KnownSimple.IsKnownSimple (SpanAction.Actor s) :=
    (h.simpleQTKE.involution_centralizer_sqtk ht).isKGroup.of_surjective
      (SpanAction.projection s) (SpanAction.projection_surjective s)
  exact SpanAction.residual_orbit_ratios_all (SpanAction.representation s) _ _ hm
    (T.isPGroup'.comap_subtype.map (SpanAction.projection s)) KnownSimple.IsKnownSimple
    (linear_cubic_residual_image_sqtk h hH hK hnf d) hkg

/-- The actual orbit construction with its structural, ratio and diagram inputs. -/
theorem linear_cubic_residual_orbit_inputs
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
      SpanAction.ResidualOrbitRatios (SpanAction.representation s) K P ∧
      NoHermitianCentralSections (SpanAction.representation s) K P := by
  obtain ⟨hs,hd⟩ := linear_cubic_residual_orbit_fitting_section D h hH hK hnf hlinear d
  exact ⟨hs,linear_cubic_residual_orbit_ratios h hH hK hnf hlinear d,hd⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
