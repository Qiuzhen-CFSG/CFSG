module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.SourceConstraints

/-!
# Initial exclusions for the terminal FF action

The source's commutator generation and four-dimensional seed exclude the
trivial actor, the S₃ case and the hyperplane case of B.5.6. The resulting
three alternatives retain all action and extension clauses of B.5.1 and
B.5.6(3),(4).

The remaining model comparison must exclude the S₆, S₇ and G₂(2) full
quotients and, in the triple-cover branch, identify the offender image and
its irreducible six-dimensional representation. Those conclusions, and
hence existence of `ExceptionalCase`, are not asserted by this reduction.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, B.5.6,
printed p.105, and the final proof of 15.3.1, printed p.1155 (combined
manuscript, 1 March 2004).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions

open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- The source commutator seed excludes the degenerate B.5.3 actor. -/
theorem not_trivial : ¬ Subsingleton d.offenderGroup := by
  intro h
  let _ := h
  apply d.offenderGroup_ne_bot
  apply le_bot_iff.mp
  intro g hg
  exact congrArg Subtype.val (Subsingleton.elim (⟨g, hg⟩ : d.offenderGroup) 1)

/-- B.5.6(2)'s moved space is too small to contain the source V. -/
theorem not_symmetricThree : ¬ Nonempty (SymmetricThreeCase d.offenderAction) := by
  rintro ⟨c⟩
  have hc := c.dimension
  rw [d.offenderAction_moved_eq_top, finrank_top] at hc
  have hd := d.module_finrank_ge_four
  omega

/-- Full commutator generation excludes the genuine codimension-one case. -/
theorem not_hyperplane : ¬ Nonempty (HyperplaneCase d.offenderAction) := by
  rintro ⟨c⟩
  have hc := c.hyperplane
  rw [d.offenderAction_moved_eq_top, top_sup_eq] at hc
  have hz : Module.finrank (ZMod 2)
      (Additive (moduleClosure V) ⧸ (⊤ : Submodule (ZMod 2) (Additive (moduleClosure V)))) = 0 :=
    Module.finrank_zero_of_subsingleton
  omega

/-- Exhaustive preliminary reduction retaining the full surviving source
records, including their nonsplit extensions and fixed summands. -/
theorem remaining_source_cases (h : SourceAlternative d.offenderAction) :
    (IsQuasisimple (generalizedFitting d.offenderGroup) ∧
      Nonempty (QuasisimpleSourceConclusion d.offenderAction
        (generalizedFitting d.offenderGroup))) ∨
    Nonempty (SourceTwoFactorCase d.offenderAction) ∨
    Nonempty (OuterSixThreeCase d.offenderAction) := by
  cases h with
  | trivial ht => exact (not_trivial d ht).elim
  | quasisimple hq c => exact Or.inl ⟨hq, ⟨c⟩⟩
  | symmetricThree c => exact (not_symmetricThree d ⟨c⟩).elim
  | twoFactors c => exact Or.inr (Or.inl ⟨c⟩)
  | outerSixThree c => exact Or.inr (Or.inr ⟨c⟩)
  | hyperplane c => exact (not_hyperplane d ⟨c⟩).elim

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions
