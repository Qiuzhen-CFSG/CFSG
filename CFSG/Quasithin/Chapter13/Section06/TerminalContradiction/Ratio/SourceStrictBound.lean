module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.NativeStrictBound
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.JankoTwoSource
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.MathieuSource

/-!
# The terminal A₅ strict ratio from proved model calculations

The complete source component conclusion marks the residual image as PSL₃(4),
M₂₃ or J₂. Their original faithful component-irreducible actions have strict
quadratic ratio greater than two by the proved linear and sporadic source
calculations. The independent degree-four obstruction permits passage from
the actual U_H/V₁ action to a faithful component-irreducible section, preserving
any small quadratic actor. This proves the strict bound on that actual action.

No universal B.4.2 or B.4.5 classification is a premise. The literal quotient
maps, generalized Fitting subgroup and complete component conclusion are kept.
Source: Aschbacher–Smith B.4.2–5 and terminal §13.6, pp.86–87,935.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.SourceStrictBound
open StrictBound Section08
universe u v

private theorem exceptionalModel_comap {L M : Type*} [Group L] [Group M]
    (e : L ≃* M) (hm : ExceptionalModel M) : ExceptionalModel L := by
  unfold ExceptionalModel at hm ⊢
  rcases hm with hm | hm | hm
  all_goals obtain ⟨f⟩ := hm
  · exact .inl ⟨e.trans f⟩
  · exact .inr (.inl ⟨e.trans f⟩)
  · exact .inr (.inr ⟨e.trans f⟩)

/-- All three terminal exceptional source actions satisfy the strict bound. -/
theorem quadraticRatio_gt_two_of_exceptional
    {D : Type u} [Group D] [Finite D] {V : Type v}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V)
    (hyp : B4Hypotheses KnownSimple.IsKnownSimple ρ)
    (hz : center (generalizedFitting D) = ⊥)
    (hm : ExceptionalModel (generalizedFitting D)) :
    2 < quadraticRatio ρ := by
  by_contra! hq
  have h : ChapterK.RankOne.SourceHypotheses ρ (generalizedFitting D) :=
    ⟨hyp.sqtk,rfl,hyp.quasisimple,hyp.faithful,hyp.irreducible,
      (Representation.BinaryOffender.cubicRatio_le_quadraticRatio ρ).trans hq⟩
  unfold ExceptionalModel at hm
  rcases hm with hm | hm | hm
  all_goals obtain ⟨e⟩ := hm
  · exact (not_lt_of_ge hq)
      (NativeStrictBound.quadraticRatio_gt_two_of_linearThreeFour ρ hyp hz e)
  · exact (not_lt_of_ge hq) (MathieuSource.quadraticRatio_gt_two h hz e)
  · exact (not_lt_of_ge hq) (JankoTwoSource.quadraticRatio_gt_two h hz e)

/-- The strict bound for the literal star action, with all classification inputs proved. -/
theorem quadraticRatio_gt_two_of_source
    {G : Type u} [Group G] [Finite G]
    (H V₃ V₁ : Subgroup G) [IsElementaryAbelian 2 (Source.UH H V₃)]
    (hn : H ≤ normalizer (V₁ : Set G))
    (hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H)
    (S : Subgroup H) (hs : Components.Conclusion S)
    (hsqtk : IsSQTK KnownSimple.IsKnownSimple (Source.Hstar H)) :
    2 < quadraticRatio (starRepresentation H V₃ V₁ hn hk) := by
  have hz := residual_center_of_source H S hs
  by_contra! hsmall
  obtain ⟨U, N, A, I, D, hD, _, _, _, _, _, _, _, _, _, _, _, hyp, hq, ⟨e⟩⟩ :=
    component_action_of_source H V₃ V₁ hn hk S hs hz hsqtk
      (disjoint_residual_rank_le_two_of_source H S hs)
      (NativeStrictBound.component_constituent_degree_gt_four H V₃ V₁ hn hk S hs hsqtk) hsmall
  let : Finite (U.toSubmodule ⧸ N.toSubmodule) :=
    Finite.of_surjective _ N.toSubmodule.mkQ_surjective
  have hzD : center (generalizedFitting D) = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [Nat.card_congr (centerCongr e).toEquiv, hz]
    exact Subgroup.card_bot
  exact (not_lt_of_ge hq) (quadraticRatio_gt_two_of_exceptional
    (restrictedRepresentation N.quotientRepresentation D I.toSubmodule hD)
    hyp hzD (exceptionalModel_comap e (residual_model_of_source H S hs).2))

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.SourceStrictBound
