module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Setup

/-!
# Remaining contracts for the cubic product deduction

These definitions separate the unproved group geometry from the unproved
section comparison. They are proof obligations, not extra source hypotheses
or assertions of the classification theorem. Products.lean proves their
conditional application to the original representation and ambient group.

Source: Aschbacher–Smith B.5.6(3),(5), p.105; 13.6.10, p.928.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

namespace Products
variable {E : Type*} [Group E]

/-- An explicit prerequisite contract. Its producer must derive the normality
and placement of every Sylow-normalized subnormal cubic in this product. -/
def CubicFactorPosition (F₁ F₂ : Subgroup E) : Prop :=
  ∀ (B : Subgroup E) (R : Sylow 2 E), B.IsSubnormal → Nat.card B = 3 →
    (R : Subgroup E) ≤ normalizer (B : Set E) →
    B.Normal ∧ ((B ≤ F₁ ∧ Nonempty (F₁ ≃* Equiv.Perm (Fin 3))) ∨
      (B ≤ F₂ ∧ Nonempty (F₂ ≃* Equiv.Perm (Fin 3))))

/-- The group-only catalogue needed to control conjugation by the ambient D.
This definition asserts no existence of the catalogue. -/
def NormalCubicCatalogue (E : Type*) [Group E] : Prop :=
  ∃ B₁ B₂ : Subgroup E, ∀ B : Subgroup E,
    B.Normal → Nat.card B = 3 → B = B₁ ∨ B = B₂

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) E W)

/-- The exact module comparison obligation for all B.5.6(3) factor actions. -/
def CubicFactorSections : Prop :=
  ∀ (F : Subgroup E) (U : Subrepresentation σ), SourceFactorCase σ F U →
    Nonempty (F ≃* Equiv.Perm (Fin 3)) →
    Module.finrank (ZMod 2) ((fixed σ).quotientImage U).toSubmodule = 2

/-- The exact internal fixed-quotient comparison, retaining both B.5.6(5)
second-factor alternatives. -/
def CubicHyperplaneSections : Prop :=
  ∀ (F : Subgroup E) (U : Subrepresentation σ), HyperplaneSecondCase σ F U →
    Nonempty (F ≃* Equiv.Perm (Fin 3)) →
    Module.finrank (ZMod 2) (U.toSubmodule ⧸ (Representation.invariants (U.toRepresentation.comp F.subtype))) = 2
end Products
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification
