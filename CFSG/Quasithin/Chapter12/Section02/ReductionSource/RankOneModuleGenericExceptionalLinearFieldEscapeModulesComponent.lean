module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.PSL3FourExclusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesFitting
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesComponent
public import Theory.GroupTheory.GeneralizedFitting.NormalComponentCentralizer
public import Theory.GroupTheory.QuotientActionImageCentralizer

/-!
# The residual and centralizer components in the original cubic escape

For the original G₁ = C_G(z), the image K* of O²(H) in the faithful action
on the centralizer span modulo ⟨z⟩ is normal and actually PSL₃(4). The image
of C₁ = C_G₁(O²(H)/O₂(O²(H))) is exactly C_G₁*(K*), and still has order
prime to three. This gives the source generalized-Fitting decomposition.

Under the small cubic bound, the existing D.2.13 minimum offender now
moves K* or an actual component of its centralizer. The cubic bound,
Suzuki identification, and D.3/B.4 constituent obstruction remain source
obligations; none is encoded in this component selection.
Source: Aschbacher--Smith 5.1.16(1) and 5.1.23, printed pp.639--640,645--646
of `refs/quasithin.pdf`.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H C : Subgroup G} {z : G}

theorem linear_cubic_residual_image
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (d : CubicEscape.LocalData T H C z) :
    let s := linear_cubic_centralizer_setup h d
    let K := ((residual H).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
    K.Normal ∧ ClassicalGroup.IsPSL K 3 4 := by
  let s := linear_cubic_centralizer_setup h d
  have hHC : H ≤ centralizer ({z} : Set G) := by
    simpa only [zpowers_eq_closure,centralizer_closure] using d.H_centralizes_point
  have hn := point_centralizer_le_residual_normalizer
    h.simpleQTKE hH.1.1 hK hnf d.point_mem d.point_ne
  let e := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let q := QuotientGroup.congr (pCore 2 (pResidual 2 H)) (pCore 2 (residual H))
    e (pCore_map_iso 2 e)
  let j := d.normalSubgroupQuotientEquiv s hHC (residual H) (map_subtype_le _) hn
  have hN : ((residual H).subgroupOf (centralizer ({z} : Set G))).Normal :=
    normal_subgroupOf_of_le_normalizer hn
  exact ⟨Normal.map hN (SpanAction.projection s) (SpanAction.projection_surjective s),
    hlinear.of_mulEquiv (q.trans j).symm⟩

theorem linear_cubic_centralizer_image
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (d : CubicEscape.LocalData T H C z) :
    let s := linear_cubic_centralizer_setup h d
    let i := inclusion (point_centralizer_le_residual_normalizer
      h.simpleQTKE hH.1.1 hK hnf d.point_mem d.point_ne)
    let K := ((residual H).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
    (((linearResidualAction H).comp i).ker).map (SpanAction.projection s) =
      centralizer (K : Set (SpanAction.Actor s)) := by
  let s := linear_cubic_centralizer_setup h d
  have hHC : H ≤ centralizer ({z} : Set G) := by
    simpa only [zpowers_eq_closure,centralizer_closure] using d.H_centralizes_point
  have hn := point_centralizer_le_residual_normalizer
    h.simpleQTKE hH.1.1 hK hnf d.point_mem d.point_ne
  exact quotient_action_kernel_map_eq_centralizer _ _ ((map_subtype_le _).trans hHC) hn
    (pCore 2 (residual H)) (SpanAction.projection s) (SpanAction.projection_surjective s)
    (d.normal_subgroup_kernel s hHC (residual H) (map_subtype_le _) hn)

theorem linear_cubic_residual_centralizer_three_prime
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (d : CubicEscape.LocalData T H C z) :
    let s := linear_cubic_centralizer_setup h d
    let K := ((residual H).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
    Nat.Coprime 3 (Nat.card (centralizer (K : Set (SpanAction.Actor s)))) := by
  dsimp only
  let s := linear_cubic_centralizer_setup h d
  let i := inclusion (point_centralizer_le_residual_normalizer
    h.simpleQTKE hH.1.1 hK hnf d.point_mem d.point_ne)
  let C₁ := ((linearResidualAction H).comp i).ker
  have h3 : Nat.Coprime 3 (Nat.card (C₁.map (SpanAction.projection s))) :=
    (linear_cubic_point_action_kernel_three_prime h hH hK hnf hlinear d).coprime_dvd_right
      (card_map_dvd _ _)
  have hcard : Nat.card (C₁.map (SpanAction.projection s)) =
      Nat.card (centralizer
        ((((residual H).subgroupOf (centralizer ({z} : Set G))).map
          (SpanAction.projection s)) : Set (SpanAction.Actor s))) :=
    Nat.card_congr (MulEquiv.subgroupCongr
      (linear_cubic_centralizer_image h hH hK hnf d)).toEquiv
  rw [← hcard]
  exact h3

theorem linear_cubic_generalizedFitting
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (d : CubicEscape.LocalData T H C z) :
    let s := linear_cubic_centralizer_setup h d
    let K := ((residual H).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
    generalizedFitting (SpanAction.Actor s) = K ⊔
      (generalizedFitting (centralizer (K : Set (SpanAction.Actor s)))).map
        (centralizer (K : Set (SpanAction.Actor s))).subtype := by
  obtain ⟨hn,hm⟩ := linear_cubic_residual_image h hH hK hnf hlinear d
  let := hn
  let := (ChapterK.Linear.Recognition.PSL3FourExclusion.model_facts hm).1
  exact generalizedFitting_eq_normal_component_sup_centralizer _

theorem linear_cubic_minimum_moves_component
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (d : CubicEscape.LocalData T H C z)
    (hsmall : cubicRatio (SpanAction.representation (linear_cubic_centralizer_setup h d)) < 2) :
    let s := linear_cubic_centralizer_setup h d
    let K := ((residual H).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
    let Z := centralizer (K : Set (SpanAction.Actor s))
    ∃ E : Subgroup (SpanAction.Actor s),
      E ≤ ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))).map
        (SpanAction.projection s) ∧ E ∈ ChapterD.QhatStar (SpanAction.representation s) ∧
      (⁅K,E⁆ ≠ ⊥ ∨ ∃ J : Subgroup Z, IsComponent Z J ∧
        IsComponent (SpanAction.Actor s) (J.map Z.subtype) ∧ ⁅J.map Z.subtype,E⁆ ≠ ⊥) := by
  obtain ⟨hn,hm⟩ := linear_cubic_residual_image h hH hK hnf hlinear d
  let := hn
  let := (ChapterK.Linear.Recognition.PSL3FourExclusion.model_facts hm).1
  obtain ⟨E,hET,hE,hF⟩ := linear_cubic_minimum_fitting_centralization h hH hK hnf hlinear d hsmall
  rw [linear_cubic_centralizer_image h hH hK hnf d] at hF
  let := hE.1.2.1.2
  exact ⟨E,hET,hE,moves_normal_component_or_centralizer_component _ E
    (IsElementaryAbelian.isPGroup 2 E) hE.1.2.1.1
    (SpanAction.actor_core_eq_bot _) hF⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
