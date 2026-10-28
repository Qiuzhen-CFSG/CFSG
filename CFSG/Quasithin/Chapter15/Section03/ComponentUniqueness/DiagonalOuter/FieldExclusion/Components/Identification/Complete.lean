module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.EvenModels.Complete
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.FiniteModels.Complete
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.OddModels

/-!
# The selected field component has one of three simple central quotients

The full Theorem C catalogue is exhausted using the marked ordinary fixed
component PSL₃(2), leaving PSL₃(4), J₂ and PSL₃(7). Genuine universal A/C
then apply this sieve to the central quotient of the component selected in
C_G(f). No exceptional-cover classification or universal A.3.18 is assumed.

Source: Aschbacher–Smith, proof of 15.3.38, printed p.1137.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
open Subgroup Theory.GroupTheory ChapterA.Section02
universe u
/-- Exhaust the source catalogue using the marked ordinary fixed component. -/
theorem SimpleInput.three_models {S : Type u} [Group S] [Finite S]
    (s : SimpleInput S) (h : ChapterA.Section02.IsTheoremCModel S) :
    Nonempty (S ≃* Matrix.PSL3Four.PSL) ∨
      Nonempty (S ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 7)) := by
  cases h with
  | alternating n hn he => exact (s.not_alternating hn he).elim
  | odd h => exact .inr (.inr (s.odd_model_equiv_psl3_seven h))
  | bender h => exact (s.not_bender h).elim
  | rank_two n h => exact .inl (s.even_rank_two_equiv_four h)
  | linear_binary n hn he => exact (s.not_binary_linear hn he).elim
  | sporadic h =>
    rcases s.sporadic_remaining h with h | h | h | h | h | h | h
    · exact .inr (.inl h)
    · exact (s.not_m22 h).elim
    · exact (s.not_m24 h).elim
    · exact (s.not_janko_four h).elim
    · exact (s.not_higman_sims h).elim
    · exact (s.not_held h).elim
    · exact (s.not_rudvalis h).elim

/-- The exact selected-component source contract used by `Reduction.field_exclusion`.
Theorem A and C are the complete earlier source statements. -/
theorem Input.fieldComponentQuotient {G : Type u} [Group G] [Finite G]
    {H K : Subgroup G} {v : G} (d : Input H K v)
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      TheoremA CFSG.KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      TheoremC CFSG.KnownSimple.IsKnownSimple X) : FieldComponentQuotient K := by
  obtain ⟨s⟩ := d.exists_simpleInput hA
  exact s.three_models (d.centralQuotient_theoremC hA hC)
end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
