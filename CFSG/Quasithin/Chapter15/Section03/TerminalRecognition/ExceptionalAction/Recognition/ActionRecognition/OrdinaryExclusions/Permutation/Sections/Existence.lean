module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Permutation.Sections.Existence.Six
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Permutation.Sections.Existence.Seven

/-!
# The actual natural central sections in the terminal permutation branches

The complete supplied FF alternative yields a natural moved central section
for the full quotient S₆ or S₇. Alternating offender images are excluded using
the faithful four-dimensional sections: the marked four-group core in degree
six, and the small-index obstruction in A₈ in degree seven. The surviving full
offender image is identified by B.5.1's outer-action clause, retaining the
original central quotient and its full quotient action.

Source: Aschbacher–Smith, B.5.1 and B.5.6, printed pp.99 and 105, and
the final proof of 15.3.1, p.1155 (combined manuscript, 1 March 2004).
-/

public section
open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.Permutation
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- The supplied full classification constructs the actual moved central
section, without a natural-action or section-existence premise. -/
theorem exists_naturalSection {n : ℕ} (hn : n = 6 ∨ n = 7)
    (h : SourceAlternative d.offenderAction)
    (e : coreQuotient H ≃* Equiv.Perm (Fin n)) : Nonempty (NaturalSection d n) := by
  rcases hn with rfl | rfl
  · exact naturalSection_six d e h
  · exact naturalSection_seven d e h

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.Permutation
