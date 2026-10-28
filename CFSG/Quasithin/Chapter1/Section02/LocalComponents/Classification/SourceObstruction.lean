module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.CenterFrattiniSource.Counterexample
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.QuotientActions

/-!
# The center–Frattini obstruction persists with the actual action data

The concrete group (C₁₂₁ × C₁₂₁) ⋊ SL₂(5) constructed in
`CenterFrattiniSource` satisfies the finite/SQTK/trivial-two-core hypotheses,
is itself a C-component, and satisfies every clause of A.3.6. Its trivial
ordinary component layer makes it nonquasisimple. The proved A.3.6 action
theorem therefore supplies all the actual omega actions, including their
common Fitting kernel and Sylow irreducibility. Even with these data the
group fails every alternative of the printed Chapter 1 conclusion.

Consequently the missing center–Frattini equality cannot be recovered by
adding those action facts to the intrinsic A.3 hypotheses. To complete
Proposition 1.2.1(4), an argument must use its ambient hypotheses: a simple
QTKE group G, H ∈ H(G), and the image of a C-component of H in H/O₂(H).
No realization of the counterexample in that setup is asserted here.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, A.3.4–A.3.6,
printed pp.43–45, Notation 1.0.1, p.499, and Proposition 1.2.1(4), p.504.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.CenterFrattiniSource

private theorem source_counterexample_not_quasisimple :
    ¬ IsQuasisimple (⊤ : Subgroup Candidate) := by
  intro h
  have hc : IsComponent Candidate ⊤ := ⟨IsSubnormal.top, h⟩
  have hle : (⊤ : Subgroup Candidate) ≤ componentLayer Candidate := le_sSup hc
  rw [componentLayer_eq_bot] at hle
  exact (candidate_isCComponent complementEquivSL5).ne_bot (bot_unique hle)

/-- The intrinsic counterexample also has every proved omega-action assertion.
There is no assumed representation, order, rank or classification premise. -/
theorem intrinsic_counterexample_with_omega_actions :
    Finite Candidate ∧
      IsSQTK CFSG.KnownSimple.IsConstructedCarrier Candidate ∧
      pCore 2 Candidate = ⊥ ∧
      (⊤ : Subgroup Candidate).IsCComponent ∧
      A36Conclusion (⊤ : Subgroup Candidate) ∧
      A36Nilpotent (⊤ : Subgroup Candidate) ∧
      OmegaActionData (⊤ : Subgroup Candidate) ∧
      ¬ CenterFrattini (⊤ : Subgroup Candidate) ∧
      ¬ Proposition121Four (⊤ : Subgroup Candidate) := by
  obtain ⟨hf, hs, ho, hK, hn, hc, hz, hfour⟩ := intrinsic_counterexample
  have h := strengthened_omega_actions hs ho hK ⟨.nilpotent hn, hc⟩
  exact ⟨hf, hs, ho, hK, h.1, hn, h.2 source_counterexample_not_quasisimple, hz, hfour⟩

/-- Actual omega actions do not repair the intrinsic implication. The source
theorem in a simple QTKE ambient group remains a distinct obligation. -/
theorem not_intrinsic_proposition121Four_even_with_omega_actions :
    ¬ (∀ (X : Type) [Group X] [Finite X],
      IsSQTK CFSG.KnownSimple.IsConstructedCarrier X → pCore 2 X = ⊥ →
      ∀ K : Subgroup X, K.IsCComponent → A36Conclusion K → A36Nilpotent K →
        OmegaActionData K → Proposition121Four K) := by
  intro h
  obtain ⟨_, hs, ho, hK, ha, hn, hw, _, hfour⟩ :=
    intrinsic_counterexample_with_omega_actions
  exact hfour (h Candidate hs ho ⊤ hK ha hn hw)

end CFSG.Quasithin.Chapter1.Section02.CenterFrattiniSource
