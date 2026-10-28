module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesOrbitRatio
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesOrbitCubic

/-!
# The original residual orbit has cubic ratio greater than two

The centralizer-span geometry supplies the literal normal PSL₃(4) image,
its SQTK property, and the original Sylow diagram element. Applying the
constituent collapse and model obstruction to each already chosen
homogeneous orbit gives a strict cubic bound on that orbit's faithful
central quotient. All generalized-Fitting and irreducibility premises are
proved upstream; no replacement orbit or assumed ratio bound is used.

This completes the PSL₃(4) constituent branch of Aschbacher--Smith 5.1.23,
printed p.646, `refs/quasithin.pdf`. Middle-layer fixedness, transfer of the
small offender to a moved component orbit, and the Suzuki alternative
remain obligations of the abelian-span proof. The original H-action
strict quadratic bound is already proved in the `EscapeModules` consumer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H C : Subgroup G} {z : G}

/-- Every previously chosen homogeneous residual orbit has strict cubic
ratio above two on its literal faithful central quotient. -/
theorem linear_cubic_residual_orbit_cubicRatio_gt_two
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
    SpanAction.ResidualOrbitCubicBound (SpanAction.representation s) K P := by
  let s := linear_cubic_centralizer_setup h d
  let K := ((residual H).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
  let P := ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
  obtain ⟨hn,hm⟩ := linear_cubic_residual_image h hH hK hnf hlinear d
  let := hn
  have hP := T.isPGroup'.comap_subtype.map (SpanAction.projection s)
  have hz : orderOf z = 2 := by simpa only [Nat.card_zpowers] using d.point_card
  have hkg : IsKGroup KnownSimple.IsKnownSimple (SpanAction.Actor s) :=
    (h.simpleQTKE.involution_centralizer_sqtk hz).isKGroup.of_surjective
      (SpanAction.projection s) (SpanAction.projection_surjective s)
  obtain ⟨F,hF,hfin,hcard,j,t,a,b,ha,hb,hd⟩ :=
    linear_cubic_residual_diagram_action D h hH hK hnf hlinear d
  have hTC : (T : Subgroup G) ≤ centralizer ({z} : Set G) :=
    le_sup_right.trans s.local_le
  have ht : SpanAction.projection s (inclusion hTC t) ∈ P :=
    mem_map_of_mem (SpanAction.projection s)
      (show inclusion hTC t ∈ (T : Subgroup G).subgroupOf (centralizer ({z} : Set G)) from
        t.property)
  exact SpanAction.residual_orbit_cubic_bound (SpanAction.representation s) K P hm hP
    KnownSimple.IsKnownSimple (linear_cubic_residual_image_sqtk h hH hK hnf d) hkg
    hcard j (SpanAction.projection s (inclusion hTC t)) ht a b ha hb hd

/-- The already constructed residual orbit, with its strict cubic obstruction.
The small-ratio contradiction must still be supplied by the geometric branch. -/
theorem linear_cubic_residual_strict_orbit
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
    SpanAction.HasStrictResidualOrbit (SpanAction.representation s) K P := by
  exact SpanAction.strict_residual_orbit _ _ _
    (linear_cubic_residual_orbit_section h hH hK hnf hlinear d)
    (linear_cubic_residual_orbit_cubicRatio_gt_two D h hH hK hnf hlinear d)


end CFSG.Quasithin.Chapter12.Section02.ChosenModule
