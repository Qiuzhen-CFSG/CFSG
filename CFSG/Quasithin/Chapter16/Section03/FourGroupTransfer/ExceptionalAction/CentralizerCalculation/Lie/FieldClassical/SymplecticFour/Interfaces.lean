module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Lie.FieldClassical.Inputs
public import Theory.SpecificGroups.SymplecticFour.FieldComponent
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.OuterReduction

/-!
# Remaining inputs for the symplectic field-component calculation

Diagram coverage and symplectic cocycle descent are shared automorphism inputs.
The two additional calculations needed here are exclusion of the specified
component in an inner involution centralizer, and rigidity of the full pointwise
fixer of the embedded derived subfield group. These are explicit proof obligations,
not asserted classification theorems. The derived binary endpoint is retained.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.4(4),
16.1.7(3a), and 16.3.5, printed pp.1171–1173 and 1178–1179.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual
open CFSG.Quasithin.Chapter16.CounterexampleGeometry.CoveredPersistence
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.FieldClassical.SymplecticFour
universe u

/-- The existing shared diagram-preserving automorphism classification. -/
def DiagramCoverage : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
    ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ (g : Sp F) (σ : F ≃+* F), a = MulAut.conj g * fieldAutomorphism σ

/-- The even-degree case of the shared symplectic field-cocycle descent. -/
def FieldCocycleDescent : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ),
    1 ≤ n → Nat.card F = 2 ^ (2 * n) → ∀ g : Sp F,
      g * representative n g = 1 →
        ∃ h : Sp F, g = h * (representative n h)⁻¹

/-- Only the inner-involution exclusion consumed by the field-component branch.
The finite simple ambient model and the genuine central quotient are retained. -/
def InnerComponentExclusion : Prop :=
  ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S] [Group.IsPerfect S]
    (n : ℕ), 1 ≤ n → ClassicalGroup.IsPSp S 2 (2 ^ (2 * n)) →
    ∀ (g : S), orderOf g = 2 → ∀ P : Subgroup S,
      IsComponentIn P (MulAut.conj g).fixedSubgroup → IsPGroup 2 (center P) →
      FieldFamily.symplecticFour.DerivedAt (P ⧸ center P) (2 ^ n) → False

/-- Rigidity is required for every automorphism, including diagram-interchanging
ones. Membership in a chosen standard automorphism subgroup is not enough. -/
def ResidualFixerRigidity : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ),
    1 ≤ n → Nat.card F = 2 ^ (2 * n) →
      fixingSubgroup (MulAut (Sp F)) (FieldComponent.embedded (F := F) n : Set (Sp F)) ≤
        zpowers (representative n)

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.FieldClassical.SymplecticFour
