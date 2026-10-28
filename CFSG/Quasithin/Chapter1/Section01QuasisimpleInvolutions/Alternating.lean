module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Alternating.CenterOdd

/-!
# Alternating branches of the quasisimple involution classification

The A₆ and A₇ central-quotient branches give the full canonical model action
from the original marked involution. The multiplier bound, Schur's fixed-image
calculation and fixed-point lifting exclude the even covers. An odd center is
trivial or actually cyclic of order three; the original automorphism and
quotient marking are retained in both alternatives.

The genuine PSL₂(9) and derived projective Sp₄(2) comparisons apply the A₆
result. For all alternating degrees at most eight, perfectness and simplicity
exclude degrees below five. The A₅ and A₈ cases give precisely PSL₂(4) and
PSL₄(2), respectively, for the parent classifier's even-family assembly.
Source: Aschbacher--Smith, 1.1.5(3), printed pp.501--503.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions.Alternating
open Chapter15.Section03.Candidates.ComponentStructure

variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    {α : MulAut L} {P : Sylow 2 L}

/-- The complete A₆ quotient branch, retaining the original marked action.
Inner actions give the Lie alternative; outer actions give the actual
transposition model on the simple group or its triple cover. -/
theorem six_of_quotient (d : MarkedInvolution α P)
    (e : L ⧸ center L ≃* alternatingGroup (Fin 6)) : ModelAction115 L α :=
  six_of_odd_center d e (center_odd_of_exceptional_quotient d e (Or.inl rfl))

/-- The complete A₇ quotient branch with cycle type `2³` on the actual
simple or triple-cover model. -/
theorem seven_of_quotient (d : MarkedInvolution α P)
    (e : L ⧸ center L ≃* alternatingGroup (Fin 7)) : ModelAction115 L α :=
  seven_of_odd_center d e (center_odd_of_exceptional_quotient d e (Or.inr rfl))

/-- The genuine derived projective Sp₄(2) application, taking the
commutator after the projective quotient as in the source convention. -/
theorem projective_derived (d : MarkedInvolution α P)
    (e : L ⧸ center L ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) :
    ModelAction115 L α :=
  six_of_quotient d (equiv_six_of_projective_derived e)

/-- The complete application to any actual PSL₂(9) quotient model. -/
theorem psl_nine (d : MarkedInvolution α P)
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 2 9) : ModelAction115 L α := by
  obtain ⟨e⟩ := equiv_six_of_psl_nine h
  exact six_of_quotient d e

/-- All alternating quotient degrees at most eight: A₆ and A₇ have their
full marked conclusions; A₅ and A₈ give the exact PSL₂(4) and PSL₄(2)
inputs to the even-family classifier, whose owner treats their covers. -/
theorem small_quotient_modelAction (d : MarkedInvolution α P) {n : ℕ}
    (hn : n ≤ 8) (e : L ⧸ center L ≃* alternatingGroup (Fin n)) :
    ModelAction115 L α ∨ ClassicalGroup.IsPSL (L ⧸ center L) 2 4 ∨
      ClassicalGroup.IsPSL (L ⧸ center L) 4 2 := by
  rcases small_quotient_cases hn e with h | h
  · exact .inr (.inl h)
  · rcases h with h | h
    · obtain ⟨e₆⟩ := h
      exact .inl (six_of_quotient d e₆)
    · rcases h with h | h
      · obtain ⟨e₇⟩ := h
        exact .inl (seven_of_quotient d e₇)
      · exact .inr (.inr h)

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions.Alternating
