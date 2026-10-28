module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesGeometry
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesCentralizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesAction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesFitting

/-!
# The Fitting step on the original escaping-cubic span

For G₁ = C_G(z), the action on the G₁-span of the plane modulo ⟨z⟩ is
constructed by the G.2.2 quotient maps. The original kernel of the action
on O²(H)/O₂(O²(H)) has order prime to three. Its image in the faithful
span action is normal and still has order prime to three.

If this action has cubic ratio below two, minimum selection and D.2.13
produce a minimum offender in the image of the original Sylow subgroup
that centralizes the Fitting subgroup of this kernel image. The geometric
small cubic bound and subsequent component argument remain separate
obligations in the proof of the abelian-span assertion.

Source: Aschbacher--Smith 5.1.16(1), 5.1.23 and D.2.13,
printed pp.639--640,645--646 and 184--185 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H C : Subgroup G} {z : G}

/-- The original three-prime centralizer image has Fitting subgroup fixed by
an actual minimum cubic offender in the original Sylow image. -/
theorem linear_cubic_minimum_fitting_centralization
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (d : CubicEscape.LocalData T H C z) :
    let s := linear_cubic_centralizer_setup h d
    let i := inclusion (point_centralizer_le_residual_normalizer
      h.simpleQTKE hH.1.1 hK hnf d.point_mem d.point_ne)
    let C₁ := ((linearResidualAction H).comp i).ker
    let N := C₁.map (SpanAction.projection s)
    cubicRatio (SpanAction.representation s) < 2 →
      ∃ A : Subgroup (SpanAction.Actor s),
        A ≤ ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))).map
          (SpanAction.projection s) ∧
        A ∈ ChapterD.QhatStar (SpanAction.representation s) ∧
        (fittingSubgroup N).map N.subtype ≤ centralizer (A : Set (SpanAction.Actor s)) := by
  dsimp only
  intro hsmall
  let s := linear_cubic_centralizer_setup h d
  let i := inclusion (point_centralizer_le_residual_normalizer
    h.simpleQTKE hH.1.1 hK hnf d.point_mem d.point_ne)
  let C₁ := ((linearResidualAction H).comp i).ker
  let f := SpanAction.projection s
  let N := C₁.map f
  let hC₁ : C₁.Normal := inferInstanceAs (((linearResidualAction H).comp i).ker.Normal)
  let : N.Normal := Normal.map hC₁ f (SpanAction.projection_surjective s)
  have h3 : Nat.Coprime 3 (Nat.card N) :=
    (linear_cubic_point_action_kernel_three_prime h hH hK hnf hlinear d).coprime_dvd_right
      (C₁.card_map_dvd f)
  have hTC : (T : Subgroup G) ≤ centralizer ({z} : Set G) :=
    le_sup_right.trans s.local_le
  let P := (T.subtype hTC).mapSurjective (SpanAction.projection_surjective s)
  obtain ⟨A, hAP, hA, hfit⟩ := exists_starred_in_sylow_centralizes_three_prime_fitting
    (SpanAction.representation s) (SpanAction.representation_faithful s)
    (SpanAction.actor_core_eq_bot s) hsmall N h3 P
  exact ⟨A, hAP, hA, hfit⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
