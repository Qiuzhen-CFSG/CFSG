module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesComponent
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesDiagram

/-!
# The diagram obstruction on the literal escaping-cubic span

The residual kernel calculation identifies O²(H)/O₂(O²(H)) with its image
in the faithful action on the centralizer span modulo ⟨z⟩. Unique maximality
above T already supplies an original Sylow diagram actor. Transporting this
actor through the same quotient map excludes Hermitian coordinates for the
span action, independently of the marking chosen by module recognition.

This proves the diagram step required at the end of 5.1.23 for the original
groups. The small cubic bound, the Suzuki constituent exclusion, and the
construction of the invariant irreducible orbit section remain obligations
of the abelian-span proof. No irreducibility or strict-ratio callback is
assumed here. Final source assembly remains qt-d-1222-linear-field-cubic-escape.
Source: Aschbacher--Smith, 5.1.23, printed pp.645--646, `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Matrix.PSL3.LinearThree.OuterExtensions
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H C : Subgroup G} {z : G}

/-- The original Sylow element implements a nontrivial diagram action on the literal residual image. -/
theorem linear_cubic_residual_diagram_action
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (d : CubicEscape.LocalData T H C z) :
    let s := linear_cubic_centralizer_setup h d
    let hTC : (T : Subgroup G) ≤ centralizer ({z} : Set G) :=
      le_sup_right.trans s.local_le
    let K := ((residual H).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      ∃ j : K ≃* PSL(3,F), ∃ t : T, ∃ a : MulAut K, ∃ b : MulAut PSL(3,F),
        (∀ k, (a k : SpanAction.Actor s) = SpanAction.projection s (inclusion hTC t) *
          k * (SpanAction.projection s (inclusion hTC t))⁻¹) ∧
        (∀ k, j (a k) = b (j k)) ∧ b ∉ diagramTrivial F := by
  let s := linear_cubic_centralizer_setup h d
  have hHC : H ≤ centralizer ({z} : Set G) := by
    simpa only [zpowers_eq_closure,centralizer_closure] using d.H_centralizes_point
  have hn := point_centralizer_le_residual_normalizer
    h.simpleQTKE hH.1.1 hK hnf d.point_mem d.point_ne
  exact graph_action_on_quotient_image (T : Subgroup G) (residual H) (centralizer ({z} : Set G))
    ((map_subtype_le _).trans hHC) (le_sup_right.trans s.local_le)
    (linear_residual_graph_action T D.sylow_normalizes_component hH hlinear)
    (SpanAction.projection s)
    (d.normalSubgroupQuotientEquiv s hHC (residual H) (map_subtype_le _) hn)
    (d.normalSubgroupQuotientEquiv_apply s hHC (residual H) (map_subtype_le _) hn)

/-- The literal centralizer-span representation cannot be the Hermitian row.
No arbitrary diagram actor or independent quotient map is assumed. -/
theorem linear_cubic_span_no_hermitian_coordinates
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (d : CubicEscape.LocalData T H C z) :
    let s := linear_cubic_centralizer_setup h d
    let K := ((residual H).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
    ¬ ∃ (j : K ≃* PSL(3,E 1))
      (c : Additive (SpanAction.moduleSubgroup s) ≃ₗ[ZMod 2] Space 1),
      ∀ k : K, ∀ w, c (SpanAction.representation s k w) =
        projectiveAction (j k) (c w) := by
  obtain ⟨F,hF,hfin,hcard,j,t,a,b,ha,hb,hd⟩ :=
    linear_cubic_residual_diagram_action D h hH hK hnf hlinear d
  exact not_hermitian_of_diagram_action _ _ hcard j _ a b ha hb hd

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
