module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.SourceContracts.Irreducible

/-!
# Source-correct B.4 inputs for the terminal ratio argument

The older `FullB42` contract uses a vector line in the triple-six case.
B.4.2(8)'s F₄-line is a projective line, hence a vector plane by K.1.3.
Here the universal B.4.2 implication uses the corrected full action list.
For the actual centerless terminal component, the triple-cover case is
impossible by its center of order three. The other cases therefore feed
the existing model comparisons without any change in their mathematics.

The intrinsic degree bound and the faithful constituent construction then
prove the strict bound for the literal action on U_H/V₁. The complete
component conclusion, including the nontrivial diagram action, remains
an input. Only the two universal earlier classifications remain unproved
inputs, owned by `qt-b-04` and discharged in the Chapter 13 assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2 and
B.4.5, printed pp.86–87; K.1.3, p.453; terminal §13.6, p.935.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource

namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.SourceClassifications
open StrictBound Section08
universe u v

/-- The complete universal B.4.2 implication, with the projective-line
convention of K.1.3. All action, generation, ratio and offender clauses
are retained; no specialized terminal conclusion is assumed. -/
def FullB42 (𝒦 : GroupClass.{u}) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (V : Type v)
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V) (A : Subgroup D),
    B42Hypotheses 𝒦 ρ A →
      ProjectiveLine.IrreducibleActionCase ρ (generalizedFitting D) (offenderSubgroup ρ)

/-- For a centerless component the two lists agree: the only differing
case has center of order three and so cannot occur. This does not assert
an implication between the unrestricted universal classification inputs. -/
theorem actionCase_of_center_eq_bot
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {L H : Subgroup D}
    (hz : center L = ⊥) (h : ProjectiveLine.IrreducibleActionCase ρ L H) :
    IrreducibleActionCase ρ L H := by
  cases h with
  | linearTwo F hg e ho hq => exact .linearTwo F hg e ho hq
  | linearThree F hg e hq => exact .linearThree F hg e hq
  | symplectic F hn hg e hq => exact .symplectic F hn hg e hq
  | symplecticTwo e hq => exact .symplecticTwo e hq
  | g2 F hn hg e ho hq => exact .g2 F hn hg e ho hq
  | g2Two e ho hq => exact .g2Two e ho hq
  | symmetric n hn e ho hq => exact .symmetric n hn e ho hq
  | alternatingSix hg e ho hq => exact .alternatingSix hg e ho hq
  | alternatingSeven hg hw e hd ho hq => exact .alternatingSeven hg hw e hd ho hq
  | tripleSix _ a _ =>
    have hc := Nat.card_congr a.centerEquiv.toEquiv
    rw [hz] at hc
    norm_num at hc
  | binaryLinear d hd hg e hq => exact .binaryLinear d hd hg e hq
  | orthogonalSix hg hw e ho hq => exact .orthogonalSix hg hw e ho hq
  | symmetricEight hw e hq => exact .symmetricEight hw e hq
  | exteriorFive hg hw e hd ho hq => exact .exteriorFive hg hw e hd ho hq

/-- The corrected full B.4.2 contract and the full B.4.5 contract exclude
small ratio for a faithful component-irreducible exceptional action. -/
theorem quadraticRatio_gt_two_of_exceptional
    {D : Type u} [Group D] [Finite D] {V : Type v}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V)
    {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦) (hB45 : FullB45.{u,v} 𝒦)
    (hyp : B4Hypotheses 𝒦 ρ) (hz : center (generalizedFitting D) = ⊥)
    (hm : ExceptionalModel (generalizedFitting D)) :
    2 < quadraticRatio ρ := by
  by_contra! hq
  have hc : Classifications.ClassicalCompetitor (generalizedFitting D) ∨
      Classifications.FixedCompetitor (generalizedFitting D) := by
    cases hB45 D V ρ (hyp.with_quadratic_bound hq) with
    | ff hc =>
      obtain ⟨A, hA⟩ := hyp.exists_B42_of_cubic_le_one hc
      exact Classifications.competitors_of_B42 ρ hz
        (actionCase_of_center_eq_bot ρ hz (hB42 D V ρ A hA))
    | table _ _ row => exact Classifications.competitors_of_table ρ hz row hq
    | boundary _ hgt _ => exact (not_lt_of_ge hq hgt).elim
  rcases hc with hc | hc
  · exact Classifications.not_classicalCompetitor_of_exceptional hm hc
  · exact Classifications.not_fixedCompetitor_of_exceptional hm hc

private theorem exceptionalModel_comap {L M : Type*} [Group L] [Group M]
    (e : L ≃* M) (hm : ExceptionalModel M) : ExceptionalModel L := by
  unfold ExceptionalModel at hm ⊢
  rcases hm with hm | hm | hm
  all_goals obtain ⟨f⟩ := hm
  · exact .inl ⟨e.trans f⟩
  · exact .inr (.inl ⟨e.trans f⟩)
  · exact .inr (.inr ⟨e.trans f⟩)

/-- An involution bounds the ratio of a module of dimension at most four;
the source-correct irreducible classification rules out that bound. -/
theorem finrank_gt_four_of_exceptional
    {L : Type u} [Group L] [Finite L] {V : Type v}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) L V)
    {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦) (hB45 : FullB45.{u,v} 𝒦)
    (hsq : IsSQTK 𝒦 L) (hf : Function.Injective ρ)
    (hL : IsQuasisimple L) (hi : ρ.IsIrreducible) (hz : center L = ⊥)
    (hm : ExceptionalModel L) (t : L) (ht : orderOf t = 2) :
    4 < Module.finrank (ZMod 2) V := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let := hL
  have hfit : generalizedFitting L = ⊤ := top_unique
    (component_le_generalizedFitting L ⊤ ⟨.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩)
  let e : generalizedFitting L ≃* L := (MulEquiv.subgroupCongr hfit).trans topEquiv
  have hz' : center (generalizedFitting L) = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [Nat.card_congr (centerCongr e).toEquiv, hz]
    exact Subgroup.card_bot
  have hgt := quadraticRatio_gt_two_of_exceptional ρ hB42 hB45
    (Classifications.b4Hypotheses_intrinsic ρ hsq hf hL hi) hz'
    (exceptionalModel_comap e hm)
  by_contra! hdim
  exact (not_lt_of_ge (quadraticRatio_le_two_of_finrank_le_four ρ t ht hdim)) hgt

/-- The source strict bound on the actual quotient action, using complete
classifications with the correct projective-line convention. Center,
outer rank, constituent degree and classification applicability are all
proved from the component conclusion and the inherited SQTK hypothesis. -/
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
    exact finrank_gt_four_of_exceptional I.toRepresentation hB42 hB45
      (hsqtk.subgroup _) hf (residual_quasisimple_of_source H S hs) hi hz
      (residual_model_of_source H S hs).2 t ht
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
  exact (not_lt_of_ge hq) (quadraticRatio_gt_two_of_exceptional
    (restrictedRepresentation N.quotientRepresentation D I.toSubmodule hD)
    hB42 hB45 hyp hzD (exceptionalModel_comap e (residual_model_of_source H S hs).2))

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.SourceClassifications
end
