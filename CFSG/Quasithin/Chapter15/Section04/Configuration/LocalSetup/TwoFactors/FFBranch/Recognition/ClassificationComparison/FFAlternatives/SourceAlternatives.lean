module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.SourceActions

/-!
# Complete conditional FF classification interface

The alternatives retain all six B.5.1 conclusions and all the action data in
B.5.6(2)–(5). In (3c) the full B.4.8(3) record refines the existing extension
record; forgetting its extra conclusions recovers the parent's established
nonquasisimple interface. The trivial actor is retained because it satisfies
B.5.3. An actual FF witness excludes it when the parent needs that specialization.

The two universal classification implications for the selected K are explicit
inputs. The proved results here only extract group cases from those full
conclusions. They assert neither universal book theorem nor a core equality.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.3 and
B.5.6, pp.104–110, with B.4.8(3), p.91.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- The full factor alternatives, retaining B.4.8(3) in the exceptional case. -/
inductive SourceFactorCase (A : Subgroup D) (U : Subrepresentation ρ) : Prop
  | natural (moved_eq : U.toSubmodule = moved ρ A)
      (natural : FactorNatural (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype))
  | doubleNatural (F : BinaryField) (odd_degree : Odd F.degree)
      (moved_eq : U.toSubmodule = moved ρ A)
      (natural : IsRepeatedLinearNatural
        (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype) F 3 2)
  | exceptional (moved_le : moved ρ A ≤ U.toSubmodule)
      (extension : FourDimensionalSource
        (((fixed ρ).quotientImage U).toRepresentation.comp A.subtype))

/-- Forgetting the referenced offender and involution calculations gives
exactly the old factor contract, with the same actual subgroups and spaces. -/
theorem SourceFactorCase.toBasic {A : Subgroup D} {U : Subrepresentation ρ}
    (h : SourceFactorCase ρ A U) : FactorCase ρ A U := by
  cases h with
  | natural hm h => exact .natural hm h
  | doubleNatural F ho hm h => exact .doubleNatural F ho hm h
  | exceptional hm h => exact .exceptional hm (h.toBasic _)

/-- The factors are determined by their action identifications. -/
theorem SourceFactorCase.factorModel {A : Subgroup D} {U : Subrepresentation ρ}
    (h : SourceFactorCase ρ A U) : FactorModel A :=
  (h.toBasic ρ).factorModel ρ

/-- B.5.6(3), with the full referenced B.4.8(3) assertion. The decomposition
is only in V/C_V(D); no splitting of V is imposed. -/
structure SourceTwoFactorCase where
  first : Subgroup D
  second : Subgroup D
  product : InternalProduct first second
  firstSpace : Subrepresentation ρ
  secondSpace : Subrepresentation ρ
  decomposition : IsCompl ((fixed ρ).quotientImage firstSpace).toSubmodule
    ((fixed ρ).quotientImage secondSpace).toSubmodule
  firstCase : SourceFactorCase ρ first firstSpace
  secondCase : SourceFactorCase ρ second secondSpace

/-- Retain the literal factor inclusions while extracting their group models. -/
def SourceTwoFactorCase.toBasic (h : SourceTwoFactorCase ρ) : TwoFactorCase ρ where
  first := h.first
  second := h.second
  product := h.product
  firstModel := h.firstCase.factorModel ρ
  secondModel := h.secondCase.factorModel ρ
  firstSpace := h.firstSpace
  secondSpace := h.secondSpace
  decomposition := h.decomposition
  firstCase := h.firstCase.toBasic ρ
  secondCase := h.secondCase.toBasic ρ

/-- The source-complete classification conclusion, with the degenerate actor
allowed by the printed hypotheses. -/
inductive SourceAlternative : Prop
  | trivial (actor : Subsingleton D)
  | quasisimple (quasisimple : IsQuasisimple (generalizedFitting D))
      (actions : QuasisimpleSourceConclusion ρ (generalizedFitting D))
  | symmetricThree (case : SymmetricThreeCase ρ)
  | twoFactors (case : SourceTwoFactorCase ρ)
  | outerSixThree (case : OuterSixThreeCase ρ)
  | hyperplane (case : HyperplaneCase ρ)

/-- Group-case extraction from the full source alternatives. It contains no
core conclusion, and the quasisimple actor is the actual F*(D). -/
theorem SourceAlternative.groupCases (h : SourceAlternative ρ) :
    Subsingleton D ∨
      (IsQuasisimple (generalizedFitting D) ∧ QuasisimpleModel (generalizedFitting D)) ∨
      NonQuasisimpleAlternative ρ := by
  cases h with
  | trivial h => exact Or.inl h
  | quasisimple hq ha => exact Or.inr (Or.inl ⟨hq, ha.fittingModel ρ⟩)
  | symmetricThree h => exact Or.inr (Or.inr (.symmetricThree h))
  | twoFactors h => exact Or.inr (Or.inr (.twoFactors (h.toBasic ρ)))
  | outerSixThree h => exact Or.inr (Or.inr (.outerSixThree h))
  | hyperplane h => exact Or.inr (Or.inr (.hyperplane h))

/-- An FF witness removes only the trivial-actor case. -/
theorem SourceAlternative.groupCases_of_ff (h : SourceAlternative ρ) (hff : IsFFModule ρ) :
    (IsQuasisimple (generalizedFitting D) ∧ QuasisimpleModel (generalizedFitting D)) ∨
      NonQuasisimpleAlternative ρ := by
  rcases h.groupCases ρ with ht | h
  · let : Subsingleton D := ht
    let : Nontrivial D := nontrivial_of_ff ρ hff
    obtain ⟨g, hg⟩ := exists_ne (1 : D)
    exact (hg (Subsingleton.elim _ _)).elim
  · exact h

/-- Universal B.5.6 for the chosen K, with every B.5.3 hypothesis supplied
by `FFHypothesis`, including its genuine finite cover and quotient equivalence. -/
def GeneralClassificationInput (K : GroupClass.{u}) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D]
    (V : Type v) [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V), FFHypothesis K ρ → SourceAlternative ρ

/-- Both complete universal implications; no additional model or core premise. -/
structure CompleteClassificationInput (K : GroupClass.{u}) : Prop where
  quasisimple : QuasisimpleClassificationInput.{u,v} K
  general : GeneralClassificationInput.{u,v} K

/-- The conditional group extraction used by the final assembly owner. -/
theorem CompleteClassificationInput.groupCases [Finite D] {K : GroupClass.{u}}
    (h : CompleteClassificationInput.{u,v} K) (hyp : FFHypothesis K ρ) :
    Subsingleton D ∨
      (IsQuasisimple (generalizedFitting D) ∧ QuasisimpleModel (generalizedFitting D)) ∨
      NonQuasisimpleAlternative ρ :=
  (h.general D V ρ hyp).groupCases ρ

/-- The nontrivial conditional extraction, using the consumer's actual FF witness. -/
theorem CompleteClassificationInput.groupCases_of_ff [Finite D] {K : GroupClass.{u}}
    (h : CompleteClassificationInput.{u,v} K) (hyp : FFHypothesis K ρ) (hff : IsFFModule ρ) :
    (IsQuasisimple (generalizedFitting D) ∧ QuasisimpleModel (generalizedFitting D)) ∨
      NonQuasisimpleAlternative ρ :=
  (h.general D V ρ hyp).groupCases_of_ff ρ hff

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
