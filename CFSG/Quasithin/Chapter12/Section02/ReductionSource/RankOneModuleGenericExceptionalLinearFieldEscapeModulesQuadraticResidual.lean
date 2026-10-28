module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesRankOne
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesComponent
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesQuadraticResidual
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry

/-!
# The rank-one opposite image centralizes the original residual

The quotient of the original residual by its two-core is identified with
its image in the centralizer-span action. Its SQTK property follows through
that same quotient. In the remaining rank-one case, the opposite image is
a quadratic offender with fixed codimension at most two. The PSL₃(4)
quadratic-section exclusion therefore makes it centralize the residual image.

This narrows the field-four alternative without identifying the kernels of
the H-span and centralizer-span actions. It does not exclude a rank-one
actor in the residual centralizer. The chief-factor lower bound, the
middle-layer fixedness and the subsequent constituent argument remain
obligations of the abelian-span proof.

Source: Aschbacher--Smith B.4.2--5 and 5.1.23, printed pp.86--87,645--646,
refs/quasithin.pdf. Final source assembly remains
qt-d-1222-linear-field-cubic-escape.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ} {z : G}

/-- SQTK descends along the actual residual quotient and its original image map. -/
theorem linear_cubic_residual_image_sqtk
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (d : CubicEscape.LocalData T H C z) :
    let s := linear_cubic_centralizer_setup h d
    let K := ((residual H).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
    IsSQTK KnownSimple.IsKnownSimple K := by
  let s := linear_cubic_centralizer_setup h d
  have hHC : H ≤ centralizer ({z} : Set G) := by
    simpa only [zpowers_eq_closure,centralizer_closure] using d.H_centralizes_point
  have hn := point_centralizer_le_residual_normalizer
    h.simpleQTKE hH.1.1 hK hnf d.point_mem d.point_ne
  let e := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  have hsqR : IsSQTK KnownSimple.IsKnownSimple (residual H) :=
    (IsSQTK.equiv e).mp
      ((Chapter3.sqtk_of_mem_H h.simpleQTKE hH.1.1.1).subgroup (pResidual 2 H))
  have hsqQ : IsSQTK KnownSimple.IsKnownSimple ((residual H) ⧸ pCore 2 (residual H)) := by
    refine ⟨?_,hsqR.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsqR.stronglyQuasithin p hp ho)
  exact (IsSQTK.equiv (d.normalSubgroupQuotientEquiv s hHC (residual H)
    (map_subtype_le _) hn)).mp hsqQ

/-- The original rank-one opposite image centralizes the same residual PSL₃(4). -/
theorem linear_cubic_nonabelian_rank_one_centralizes_residual
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G))))
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G))
    (hrank : let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
      rank (((conjugate (S.W g) g).subgroupOf S.H).map
        (SpanAction.projection (linear_cubic_centralizer_setup h d))) = 1) :
    let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
    let s := linear_cubic_centralizer_setup h d
    let E := ((conjugate (S.W g) g).subgroupOf S.H).map (SpanAction.projection s)
    let K := ((residual H).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
    E ≤ centralizer (K : Set (SpanAction.Actor s)) := by
  let s := linear_cubic_centralizer_setup h d
  obtain ⟨hN,hm⟩ := linear_cubic_residual_image h hH hK hnf hlinear d
  let := hN
  obtain ⟨he,hq,hd,_⟩ :=
    linear_cubic_nonabelian_rank_one_offender D h hpsl c d hne g hg hgn hrank
  have ht : orderOf z = 2 := by simpa only [Nat.card_zpowers] using d.point_card
  have hkg : IsKGroup KnownSimple.IsKnownSimple (SpanAction.Actor s) :=
    (h.simpleQTKE.involution_centralizer_sqtk ht).isKGroup.of_surjective
      (SpanAction.projection s) (SpanAction.projection_surjective s)
  exact rank_one_quadratic_centralizes_residual (SpanAction.representation s) _ _
    (linear_cubic_residual_image_sqtk h hH hK hnf d) hkg hm
      (SpanAction.representation_faithful s) he hrank hq hd

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
