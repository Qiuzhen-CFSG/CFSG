module
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Transport
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Quotient
/-!
# Assembly of the proper-pair automorphism-centralizer sieve

The faithful order-four action supplies a lower bound for the pointwise fixer
of the actual embedded L. The five Lie rows and the L₃(2) row in J₂ are
excluded by their strict upper bounds. In the remaining rows, the order
bound and square identities identify the full fixer with E₄. Perfectness
transports this result to the automorphism centralizer required by
`ActionCalculation`, retaining the HS possibility for its separate elimination.

`actionCalculation_of_bounds` is conditional. The Lie, Mathieu, Janko,
Higman–Sims and Rudvalis bounds are new intrinsic obligations, not supplied
by `ProperModels`, and must all be discharged before this calculation or
16.3.5 is reported complete. This module owns that assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.7(3), printed pp.1172–1173, and 16.3.5, pp.1178–1179.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation
open Subgroup Theory.GroupTheory ClassificationModels
open CounterexampleGeometry.CoveredPersistence
variable {G : Type*} [Group G] [Finite G]

/-- Conditional assembly of all nine rows. The five model bounds are
independent obligations; this does not yet assert the intrinsic calculation. -/
theorem actionCalculation_of_bounds {E L I : Subgroup G} {t i : G}
    (h : PairContext E L I t i) (hm : ProperModels L I)
    (hlie : LieBounds L I) (hm12 : MathieuBound L I) (hj2 : JankoBounds L I)
    (hhs : HigmanSimsBound L I) (hru : RudvalisBound L I) :
    ActionCalculation L I h.proper.le := by
  have hlower : 4 ≤ Nat.card (pairFixer L I) :=
    h.card ▸ card_le_pairFixer h.normalizes h.centralizes h.faithful
  have he (hb : FourBound L I) : Nonempty
      (centralizer ((inducedAction L I (h.proper.le.trans I.le_normalizer)).range :
        Set (MulAut I)) ≃* (Fin 2 → Multiplicative (ZMod 2))) := by
    let := h.setup.component.quasisimple
    rw [action_centralizer_eq_pairFixer h.proper.le]
    exact hb.nonempty_equiv hlower
  cases hm with
  | field X n hn large small =>
    exact False.elim (not_lt_of_ge hlower (hlie.field X n hn large small))
  | graph_field_linear n hn large small =>
    exact False.elim (not_lt_of_ge hlower (hlie.graph_field_linear n hn large small))
  | graph_linear_unitary n hn large small =>
    exact False.elim (not_lt_of_ge hlower (hlie.graph_linear_unitary n hn large small))
  | graph_field_symplectic m hm large small =>
    exact False.elim (not_lt_of_ge hlower (hlie.graph_field_symplectic m hm large small))
  | graph_binary n hn large small =>
    exact False.elim (not_lt_of_ge hlower (hlie.graph_binary n hn large small))
  | mathieu_janko large small =>
    rcases large with large | large
    · exact ⟨he (hm12 large small), Or.inl (Or.inl ⟨small, Or.inl large⟩)⟩
    · exact ⟨he (hj2.alternating large small), Or.inl (Or.inl ⟨small, Or.inr large⟩)⟩
  | janko_linear large small =>
    exact False.elim (not_lt_of_ge hlower (hj2.linear large small))
  | higman_sims large small =>
    exact ⟨he (hhs large small), Or.inr large⟩
  | rudvalis large small =>
    exact ⟨he (hru large small), Or.inl (Or.inr ⟨small, large⟩)⟩
end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation
