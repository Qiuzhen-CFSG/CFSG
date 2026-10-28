module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Reduction
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Permutation.Groups
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Permutation.Sections
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Permutation.Sections.Existence
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Permutation.Sections.MarkedSeed
public import Theory.Representation.BinaryPermutation.LocalResidualSeed

/-!
# The marked S₆ and S₇ terminal FF exclusions

The complete supplied FF alternative constructs a natural moved central
section for the full quotient. This construction separately excludes the
alternating offender images; it never assumes that the offender actor is
the full quotient. The original four-dimensional seed injects through the
central kernel, retaining both fixedness under the marked residual two-core
and generation by residual commutators.

We transport the actual generating parabolics and their common Sylow subgroup
through the natural section's own group equivalence. The six- and seven-point
residual calculations then contradict the projected seed. All extra section
and model premises are discharged; only the original source input, supplied
classification alternative and full-quotient isomorphism remain.

Source: Aschbacher–Smith, B.5.1/B.5.6, printed pp.99 and 105, and the final
proof of 15.3.1, printed p.1155 (combined manuscript, 1 March 2004).
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.Permutation
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- The marked source configuration admits neither full symmetric quotient.
The supplied classification alternative constructs the natural central section;
its surviving seed contradicts the literal residual-action calculation. -/
theorem not_symmetric {n : ℕ} (hn : n = 6 ∨ n = 7)
    (h : SourceAlternative d.offenderAction)
    (e : coreQuotient H ≃* Equiv.Perm (Fin n)) : False := by
  obtain ⟨s⟩ := exists_naturalSection d hn h e
  obtain ⟨T, h₁, h₂, hi₁, hi₂⟩ := model_sylow_indices d s.natural.groupEquiv
  have hfix := s.seedMap_range_fixed
  have hcomm := s.seedMap_range_commutator
  rw [← first_model_residual d s.natural.groupEquiv] at hfix hcomm
  rcases hn with rfl | rfl
  · exact BinaryPermutation.LocalResidualSeed.six T _ _ h₁ h₂ hi₁ hi₂
      (model_goldschmidt d s.natural.groupEquiv).generated _
      s.seedMap_range_finrank hfix hcomm
  · exact BinaryPermutation.LocalResidualSeed.seven T _ _ h₁ h₂ hi₁ hi₂
      (model_goldschmidt d s.natural.groupEquiv).generated _
      s.seedMap_range_finrank hfix hcomm

/-- The S₆ full-quotient branch of the terminal FF configuration is impossible. -/
theorem not_symmetric_six (h : SourceAlternative d.offenderAction)
    (e : coreQuotient H ≃* Equiv.Perm (Fin 6)) : False :=
  not_symmetric d (Or.inl rfl) h e

/-- The S₇ full-quotient branch of the terminal FF configuration is impossible. -/
theorem not_symmetric_seven (h : SourceAlternative d.offenderAction)
    (e : coreQuotient H ≃* Equiv.Perm (Fin 7)) : False :=
  not_symmetric d (Or.inr rfl) h e
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.Permutation
