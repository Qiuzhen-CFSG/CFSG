module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Generation

/-!
# Parameter and marking consequences in 11.3.4

E.3.20 supplies the lower bound with the actual minimum n(H).
The earlier 11.2.2 values of s eliminate the G₂ marking when n(H) ≤ n;
the linear conclusion of 11.2.1 handles the other branch.
The original normalizer reduction then gives N_G(V₁) ≤ N_G(V).

Only the indicated preceding-source consequences remain explicit.
The rank-one recognition and the strict-parameter contradiction of
11.3.5--6 are not asserted here.
Source: Aschbacher--Smith, 11.3.4, printed p.771.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H : Subgroup G}

/-- The numerical part of 11.2.2 implies n ≤ n(H) in the counterexample.
The earlier s-bound is retained on the original seed. -/
theorem degree_le_parameter (h : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary) :
    S.field.degree ≤ ChapterE.generationParameter H :=
  ENat.natCast_le_natCast.mp (hs.trans (counterexample_parameter_lower h p hc))

/-- The actual SL₃/Sp₄ alternative in 11.3.4(2). The two remaining inputs
are precisely the relevant clauses of 11.2.1 and 11.2.2(3). -/
theorem linear_or_symplectic (h : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H)
    (hlarge : S.field.degree < ChapterE.generationParameter H →
      Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree))
    (hg2 : Nonempty (ActionEquiv D.centralQuotientAction
        (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))) →
      @ChapterE.globalS G _ V D.elementary = (2 * S.field.degree : ℕ)) :
    Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) := by
  by_cases hk : S.field.degree < ChapterE.generationParameter H
  · exact .inl (hlarge hk)
  · cases S.natural with
    | sl3 m =>
      exact .inl ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,⟨m.some.groupEquiv⟩⟩
    | sp4 m =>
      exact .inr ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,⟨m.some.groupEquiv⟩⟩
    | g2 m =>
      have he := counterexample_parameter_lower h p hc
      rw [hg2 m] at he
      have := ENat.natCast_le_natCast.mp he
      have := S.nonbinary
      omega

/-- The upper estimate retained from 11.2.1, together with E.3.20's genuine
lower estimate. No free numerical label replaces the generation parameter. -/
theorem parameter_bounds (h : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hupper : S.field.degree < ChapterE.generationParameter H →
      ChapterE.generationParameter H ≤ 2 * S.field.degree) :
    S.field.degree ≤ ChapterE.generationParameter H ∧
      ChapterE.generationParameter H ≤ 2 * S.field.degree := by
  refine ⟨degree_le_parameter h p hc hs,?_⟩
  by_cases hk : S.field.degree < ChapterE.generationParameter H
  · exact hupper hk
  · omega

/-- Apply the proved marking alternative to the actual source line normalizer. -/
theorem line_normalizer_le (h : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H)
    (hlarge : S.field.degree < ChapterE.generationParameter H →
      Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree))
    (hg2 : Nonempty (ActionEquiv D.centralQuotientAction
        (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))) →
      @ChapterE.globalS G _ V D.elementary = (2 * S.field.degree : ℕ)) :
    normalizer (D.centralQuotientPreimage U₁ : Set G) ≤ normalizer (V : Set G) :=
  line_normalizer_le_of_counterexample h p hc (linear_or_symplectic h p hc hlarge hg2)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
