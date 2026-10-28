module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.Basic

/-!
# The four nonquasisimple FF alternatives

These are the literal output configurations B.5.6(2)–(5). All factor maps
respect the original inclusions, and all submodules and quotient actions
belong to the given representation. In the direct-product case the direct
sum is asserted only after quotienting by the global fixed space. The
exceptional four-dimensional extensions and the hyperplane case are retained.
The outer case records conjugation by the actual element on each factor;
it imposes no splitting of the group extension.

This module defines conclusions, not a classification theorem. The
quasisimple alternative requires the full six-clause B.5.1 conclusion,
and final assembly remains in FFAlternatives.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, B.5.6, printed p.105, proof pp.106–110.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- B.5.6(2), including its full splitting and dimension assertions. -/
structure SymmetricThreeCase where
  equiv : D ≃* Equiv.Perm (Fin 3)
  decomposition : IsCompl (moved ρ ⊤) ρ.invariants
  dimension : Module.finrank (ZMod 2) (moved ρ ⊤) = 2

/-- The natural, double-natural, and exceptional extension possibilities
for the image of one invariant submodule in V/C_V(D). -/
inductive FactorCase (A : Subgroup D) (U : Subrepresentation ρ) : Prop
  | natural (moved_eq : U.toSubmodule = moved ρ A)
      (natural : FactorNatural (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype))
  | doubleNatural (F : BinaryField) (odd_degree : Odd F.degree)
      (moved_eq : U.toSubmodule = moved ρ A)
      (natural : IsRepeatedLinearNatural
        (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype) F 3 2)
  | exceptional (moved_le : moved ρ A ≤ U.toSubmodule)
      (extension : IsFourDimensionalExtension
        (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype))

/-- B.5.6(3). The invariant summands need split only modulo C_V(D). -/
structure TwoFactorCase where
  first : Subgroup D
  second : Subgroup D
  product : InternalProduct first second
  firstModel : FactorModel first
  secondModel : FactorModel second
  firstSpace : Subrepresentation ρ
  secondSpace : Subrepresentation ρ
  decomposition : IsCompl ((fixed ρ).quotientImage firstSpace).toSubmodule
    ((fixed ρ).quotientImage secondSpace).toSubmodule
  firstCase : FactorCase ρ first firstSpace
  secondCase : FactorCase ρ second secondSpace

/-- A specified element induces an outer automorphism on the actual subgroup. -/
def InducesOuter (A : Subgroup D) (t : D) : Prop :=
  ∃ α : MulAut A, (∀ a : A, (α a : D) = t * (a : D) * t⁻¹) ∧
    α ∉ (MulAut.conj (G := A)).range

/-- B.5.6(4), with the commuting factors, original conjugation action and
full vector-space direct sum. No split semidirect product is substituted
for the source's extension notation. -/
structure OuterSixThreeCase where
  first : Subgroup D
  second : Subgroup D
  product : (first × second) ≃* ↥(first ⊔ second)
  product_apply : ∀ a b, (product (a, b) : D) = (a : D) * (b : D)
  firstEquiv : first ≃* alternatingGroup (Fin 6)
  secondEquiv : second ≃* Multiplicative (ZMod 3)
  element : D
  generates : (first ⊔ second) ⊔ zpowers element = ⊤
  firstOuter : InducesOuter first element
  secondOuter : InducesOuter second element
  disjoint : Disjoint (moved ρ first) (moved ρ second)
  decomposition : IsCompl ρ.invariants (moved ρ first ⊔ moved ρ second)
  firstDimension : Module.finrank (ZMod 2) (moved ρ first) = 4 ∨
    Module.finrank (ZMod 2) (moved ρ first) = 5
  secondDimension : Module.finrank (ZMod 2) (moved ρ second) = 2

/-- The second-factor possibilities in the exceptional hyperplane case.
The second alternative retains the quotient by its own fixed space. -/
inductive HyperplaneSecondCase (B : Subgroup D) (U : Subrepresentation ρ) : Prop
  | linearThree (r : ℕ) (bound : r ≤ 2)
      (natural : IsRepeatedLinearNatural (U.toRepresentation.comp B.subtype)
        BinaryField.two 3 r)
  | linearTwo (F : BinaryField)
      (natural : IsLinearNatural (reducedAction (U.toRepresentation.comp B.subtype)) F 2)

/-- B.5.6(5): a sum inside [V,D], with [V,D]+C_V(D) of codimension one.
The first factor is the actual binary SL₃ model (equal to its projective
model), and its moved subspace has dimension three. -/
structure HyperplaneCase where
  first : Subgroup D
  second : Subgroup D
  product : InternalProduct first second
  firstEquiv : first ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
  firstDimension : Module.finrank (ZMod 2) (moved ρ first) = 3
  disjoint : Disjoint (moved ρ first) (moved ρ second)
  moved_eq : moved ρ ⊤ = moved ρ first ⊔ moved ρ second
  hyperplane : Module.finrank (ZMod 2) (V ⧸ (moved ρ ⊤ ⊔ ρ.invariants)) = 1
  secondSpace : Subrepresentation ρ
  secondSpace_eq : secondSpace.toSubmodule = moved ρ second
  secondCase : HyperplaneSecondCase ρ second secondSpace

/-- The complete disjunction B.5.6(2)–(5), before adjoining the
quasisimple and trivial-actor cases. -/
inductive NonQuasisimpleAlternative : Prop
  | symmetricThree (case : SymmetricThreeCase ρ)
  | twoFactors (case : TwoFactorCase ρ)
  | outerSixThree (case : OuterSixThreeCase ρ)
  | hyperplane (case : HyperplaneCase ρ)

/-- A natural-module identification supplies the same actor's group model. -/
theorem FactorNatural.factorModel (h : FactorNatural ρ) : FactorModel D := by
  cases h with
  | linearTwo F h =>
    obtain ⟨e⟩ := h
    exact .linearTwo F e.groupEquiv
  | symmetricFive h =>
    obtain ⟨e⟩ := h
    exact .symmetricFive e.groupEquiv
  | linearThree F ho h =>
    obtain ⟨e⟩ := h
    exact .linearThree F ho e.groupEquiv

/-- The exceptional extension also identifies its actual actor. -/
theorem IsFourDimensionalExtension.factorModel (h : IsFourDimensionalExtension ρ) :
    FactorModel D := by
  obtain ⟨_, _, W, _, ⟨e⟩⟩ := h
  exact .linearThree BinaryField.two (by decide) e.groupEquiv

/-- Every one-factor module alternative gives its literal group model. -/
theorem FactorCase.factorModel {A : Subgroup D} {U : Subrepresentation ρ}
    (h : FactorCase ρ A U) : FactorModel A := by
  cases h with
  | natural _ h => exact h.factorModel _
  | doubleNatural F ho _ h =>
    obtain ⟨e⟩ := h
    exact .linearThree F ho e.groupEquiv
  | exceptional _ h => exact h.factorModel _

/-- The hyperplane case's second actor is likewise determined by its actual
representation, including the quotient used in B.5.6(5b). -/
theorem HyperplaneSecondCase.factorModel {B : Subgroup D} {U : Subrepresentation ρ}
    (h : HyperplaneSecondCase ρ B U) : FactorModel B := by
  cases h with
  | linearThree _ _ h =>
    obtain ⟨e⟩ := h
    exact .linearThree BinaryField.two (by decide) e.groupEquiv
  | linearTwo F h =>
    obtain ⟨e⟩ := h
    exact .linearTwo F e.groupEquiv

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
