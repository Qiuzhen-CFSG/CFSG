module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesTransfer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesSuzuki

/-!
# Completing the component obstruction on the original span action

A strict small cubic bound selects the previously constructed minimum
offender and a moved three-free component of the residual centralizer.
The original centralizer supplies its SQTK cover. The Suzuki model,
five-rank normality argument and invariant-constituent endpoint now
contradict that bound, retaining the original quotient projection.
Together with the proved residual-orbit obstruction this gives
2 ≤ cubicRatio on the whole centralizer-span action.

Consequently middle-layer fixedness is the only extra premise in the
abelian-span consumer below: the chief count already supplies strict
rank growth. This conditional consumer is not source 5.1.23; its fixedness
premise must still be discharged from the original ambient hypotheses.
The original H-action strict quadratic bound is already proved in Modules.

Source: Aschbacher--Smith 5.1.23 and the end of 5.1.14,
printed pp.645--646, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ} {z : G}

/-- Both component alternatives exclude a strict small cubic bound on the original span action. -/
theorem linear_cubic_cubicRatio_ge_two
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (d : CubicEscape.LocalData T H C z) :
    2 ≤ cubicRatio (SpanAction.representation (linear_cubic_centralizer_setup h d)) := by
  apply le_of_not_gt
  intro hsmall
  let s := linear_cubic_centralizer_setup h d
  let K := ((residual H).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
  let Z := centralizer (K : Set (SpanAction.Actor s))
  obtain ⟨E,_hEP,hE,_hEZ,_hne,J,_hJ,hJX,h3,_hm,hm⟩ :=
    linear_cubic_minimum_moves_centralizer_component D h hH hK hnf hlinear d hsmall
  obtain ⟨hN,hmodel⟩ := linear_cubic_residual_image h hH hK hnf hlinear d
  let := hN
  have ht : orderOf z = 2 := by simpa only [Nat.card_zpowers] using d.point_card
  have hs := h.simpleQTKE.involution_centralizer_sqtk ht
  have h3' : Nat.Coprime 3 (Nat.card (J.map Z.subtype)) := by
    rwa [card_map_of_injective Z.subtype_injective]
  exact SpanAction.no_small_starred_centralizer_component
    (SpanAction.projection s) (SpanAction.projection_surjective s) hs
    (SpanAction.actor_core_eq_bot s) (SpanAction.representation s)
    (SpanAction.representation_faithful s) K (J.map Z.subtype) E hmodel hJX
    (map_subtype_le J) h3' hE hm hsmall

/-- With the sole remaining fixed-layer premise, the actual centralizer span is abelian. -/
theorem linear_cubic_abelian_span_of_middle_fixed
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z) (hn : 1 < n)
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G))
    (hfix : let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
      ⁅conjugate (S.W g) g,S.S₂ g⁆ ≤ zpowers z) :
    IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G))) := by
  by_contra hne
  exact not_lt_of_ge (linear_cubic_cubicRatio_ge_two D h hH hK hnf hlinear d)
    (linear_cubic_strict_cubic_of_middle_fixed D h hpsl c d hne hn g hg hgn hfix)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
