module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesDiagram
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesConstituent
public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.Restriction

/-!
# The original residual orbit section and its diagram obstruction

A.1.42 selects a homogeneous Irr⁺ member for the literal residual image
on the centralizer span modulo ⟨z⟩. Its orbit under the original Sylow
image has a faithful residual action on its central quotient. The
original diagram element lies in the same residual--Sylow join, so
every invariant central section, including this constructed orbit
quotient, is excluded from the Hermitian row in every marking.

This supplies the section construction and the section-level diagram
step of 5.1.23. It does not assert that the orbit quotient is irreducible:
the cubic bound, Suzuki branch and D.3.10 collapse remain in this task.
Final source assembly remains qt-d-1222-linear-field-cubic-escape.
Source: Aschbacher--Smith, printed pp.645--646, `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped MatrixGroups IsMulCommutative
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H C : Subgroup G} {z : G}

/-- The homogeneous seed is constructed on the original faithful span action. -/
theorem linear_cubic_residual_orbit_section
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (d : CubicEscape.LocalData T H C z) :
    let s := linear_cubic_centralizer_setup h d
    let K := ((residual H).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
    let P := ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
    HasFaithfulHomogeneousOrbitSection (SpanAction.representation s) K P := by
  let s := linear_cubic_centralizer_setup h d
  obtain ⟨hn,hm⟩ := linear_cubic_residual_image h hH hK hnf hlinear d
  let := hn
  exact SpanAction.exists_residual_orbit_section s _ _ hm
    (T.isPGroup'.comap_subtype.map (SpanAction.projection s))

/-- The same original diagram actor acts on every invariant central section.
This includes the orbit quotient selected above, without a whole-space hypothesis. -/
theorem linear_cubic_central_section_no_hermitian_coordinates
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
    NoHermitianCentralSections (SpanAction.representation s) K P := by
  let s := linear_cubic_centralizer_setup h d
  let K := ((residual H).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
  let P := ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
  obtain ⟨F,hF,hfin,hcard,j,t,a,b,ha,hb,hd⟩ :=
    linear_cubic_residual_diagram_action D h hH hK hnf hlinear d
  have hTC : (T : Subgroup G) ≤ centralizer ({z} : Set G) :=
    le_sup_right.trans s.local_le
  have ht : SpanAction.projection s (inclusion hTC t) ∈ P :=
    mem_map_of_mem (SpanAction.projection s)
      (show inclusion hTC t ∈ (T : Subgroup G).subgroupOf (centralizer ({z} : Set G)) from
        t.property)
  exact noHermitianCentralSections_of_diagram (SpanAction.representation s) K P hcard j
    (SpanAction.projection s (inclusion hTC t)) ht a b ha hb hd

/-- The constructed homogeneous orbit section satisfies the diagram obstruction
on its own central quotient, with faithful action of the same residual image. -/
theorem linear_cubic_residual_orbit_obstruction
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
    HasFaithfulHomogeneousOrbitSection (SpanAction.representation s) K P ∧
      NoHermitianCentralSections (SpanAction.representation s) K P := by
  exact ⟨linear_cubic_residual_orbit_section h hH hK hnf hlinear d,
    linear_cubic_central_section_no_hermitian_coordinates D h hH hK hnf hlinear d⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
