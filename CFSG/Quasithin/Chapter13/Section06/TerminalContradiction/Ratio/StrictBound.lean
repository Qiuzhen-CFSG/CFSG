module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.Source
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Models
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Sections
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.ConstituentGeometry
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Constituents
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.ModelFacts

/-!
# The strict bound in the terminal A₅ argument

`Sections` constructs a faithful H*-irreducible section of the literal
U_H/V₁ action, preserving a putative small quadratic actor and its rank.
`Models` identifies the residual image with the actual source model and
proves its quasisimplicity from the C-component and F* output.
`ModelFacts` supplies the component's trivial center, an involution, and
the rank-two bound for actors disjoint from it. The complete B.4
classifications imply that every faithful irreducible component action
has dimension greater than four. `ConstituentGeometry` then rules out
a small quadratic actor moving a constituent: its dimension would be
at most twice the actor rank, hence at most four. `Constituents` constructs
the faithful component-irreducible action of the join with that actor.
The full B.4 alternatives, compared through actual group equivalences,
contradict its small ratio. This proves the strict bound on U_H/V₁ itself.

The complete source component conclusion is retained, including its
generation, residual, and nontrivial diagram-action clauses. All local
center, rank, degree, and classification-applicability premises are
discharged. The universal `FullB42` and `FullB45` implications remain
explicit inputs owned by `qt-b-04`, with final discharge in `qt-13-06`.
`Ratio.lean` owns combination with the independent F.9 upper bound.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the last
paragraph of §13.6, printed p.935 / PDF p.952.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound
open Section08

/-- Apply the section construction to the complete explicit 13.6.27 output.
All generation and diagram clauses remain in `hs`; only triviality of the
component center remains an extra structural premise for this first passage.
This conclusion is not yet component-irreducibility or the strict bound. -/
theorem exists_bounded_section_of_source
    {G : Type*} [Group G] [Finite G]
    (H V₃ V₁ : Subgroup G) [IsElementaryAbelian 2 (Source.UH H V₃)]
    (hn : H ≤ normalizer (V₁ : Set G))
    (hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H)
    (S : Subgroup H) (hs : Components.Conclusion S)
    (hz : center (Source.starImage H (terminalResidual H)) = ⊥)
    (hsmall : quadraticRatio (starRepresentation H V₃ V₁ hn hk) ≤ 2) :
    ∃ U : Subrepresentation (starRepresentation H V₃ V₁ hn hk),
      ∃ N : Subrepresentation U.toRepresentation, ∃ A : Subgroup (Source.Hstar H),
        N.quotientRepresentation.IsIrreducible ∧
        Function.Injective N.quotientRepresentation ∧
        IsElementaryTwo A ∧ IsQuadratic N.quotientRepresentation A ∧
        fixedCodim N.quotientRepresentation A ≤ 2 * rank A := by
  obtain ⟨U, N, A, hi, hf, hA, _, _, hq, _, hc⟩ :=
    exists_bounded_faithful_irreducible_star_section H V₃ V₁ hn hk
      (residual_model_of_source H S hs).1 (residual_quasisimple_of_source H S hs) hz hsmall
  exact ⟨U, N, A, hi, hf, hA, hq, hc⟩

universe u

/-- The strict-bound half of the terminal paragraph of §13.6, on the
literal faithful H/O₂(H) action on U_H/V₁. The full source component
conclusion supplies the actual PSL₃(4), M₂₃, or J₂ marking and retains
the diagram and generation clauses. The complete universal B.4.2 and
B.4.5 implications are the only remaining classification inputs.

The structural model theorems discharge the center, involution, and
outer-rank requirements. Applying B.4 intrinsically to the component
discharges the degree obstruction in the constituent reduction. Its
resulting faithful component-irreducible action satisfies every B.4
hypothesis, so the full model comparison contradicts any ratio at most
two. The independent F.9 upper bound is combined by the parent module. -/
theorem quadraticRatio_gt_two_of_source
    {G : Type u} [Group G] [Finite G]
    (H V₃ V₁ : Subgroup G) [IsElementaryAbelian 2 (Source.UH H V₃)]
    (hn : H ≤ normalizer (V₁ : Set G))
    (hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H)
    (S : Subgroup H) (hs : Components.Conclusion S)
    {𝒦 : GroupClass.{u}} (hsqtk : IsSQTK 𝒦 (Source.Hstar H))
    (hB42 : FullB42.{u,u} 𝒦) (hB45 : FullB45.{u,u} 𝒦) :
    2 < quadraticRatio (starRepresentation H V₃ V₁ hn hk) := by
  have hz := residual_center_of_source H S hs
  obtain ⟨t, ht⟩ := residual_involution_of_source H S hs
  have hdegree : ∀
      (U : Subrepresentation (starRepresentation H V₃ V₁ hn hk))
      (N : Subrepresentation U.toRepresentation)
      (I : Subrepresentation
        (N.quotientRepresentation.comp
          (Source.starImage H (terminalResidual H)).subtype)),
      Function.Injective I.toRepresentation →
        Representation.IsIrreducible I.toRepresentation →
          4 < Module.finrank (ZMod 2) I.toSubmodule := by
    intro U N I hf hi
    let : Finite (U.toSubmodule ⧸ N.toSubmodule) :=
      Finite.of_surjective _ N.toSubmodule.mkQ_surjective
    exact Classifications.source_finrank_gt_four H S hs I.toRepresentation hB42 hB45
      (hsqtk.subgroup _) hf hi hz t ht
  by_contra! hsmall
  obtain ⟨U, N, A, I, D, hD, _, _, _, _, _, _, _, _, _, _, _, hyp, hq, ⟨e⟩⟩ :=
    component_action_of_source H V₃ V₁ hn hk S hs hz hsqtk
      (disjoint_residual_rank_le_two_of_source H S hs) hdegree hsmall
  let : Finite (U.toSubmodule ⧸ N.toSubmodule) :=
    Finite.of_surjective _ N.toSubmodule.mkQ_surjective
  have hzD : center (generalizedFitting D) = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [Nat.card_congr (centerCongr e).toEquiv, hz]
    exact Subgroup.card_bot
  exact (not_lt_of_ge hq) (Classifications.source_quadraticRatio_gt_two
    (restrictedRepresentation N.quotientRepresentation D I.toSubmodule hD)
    hB42 hB45 hyp hzD H S hs e)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound
