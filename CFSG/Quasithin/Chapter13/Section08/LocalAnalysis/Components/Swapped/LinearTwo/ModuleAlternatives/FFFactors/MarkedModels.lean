module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.MarkedModels.Groups
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.MarkedModels.Actions

/-!
# Intrinsic recognition of the marked FF factor module

Starting from one full B.5.6(3) factor case, an ordinary component
A ≅ PSL₂(2ⁿ), n ≥ 2, is located inside the classified actor C. In the SL₂
case it is C itself, with the same field exponent. In the S₅ case it is
the actual A₅ subgroup; restriction of the natural module gives its
four-dimensional even-weight core. Rank-three actors are impossible,
which excludes the rank-three natural, double-natural and exceptional
four-dimensional extension alternatives together.

With the ambient fixed space zero, the original summand is identified
with its image in the fixed-space quotient by the actual projection.
The alternating action generates the full summand by commutators, giving
the canonical equality X = [V,A] as well as the concrete action equivalence.
The source case already supplies the required action identifications, so
the conclusion does not need separate faithfulness or finite-dimension
premises beyond those in its intended source application.

This is a conditional recognition theorem from `SourceFactorCase`, not
an assertion of B.5.6 or of the branch selection in 13.8.16.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1,
B.5.6(3), printed pp.99, 105, and proof of 13.8.16(1), p.952 (PDF p.969).
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.MarkedModels
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

variable {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- The marked component acts on its literal moved space as the natural
SL₂ module of the same field degree or, when n = 2, the orthogonal A₅ core.
All three full source factor alternatives are handled. -/
theorem sourceFactorCase_recognition (hfix : ρ.invariants = ⊥)
    {C A : Subgroup D} {X : Subrepresentation ρ}
    (hcase : SourceFactorCase ρ C X) (hA : IsComponent D A) (hAC : A ≤ C)
    {n : ℕ} (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSL A 2 (2 ^ n)) :
    X.toSubmodule = subspaceCommutator ρ ⊤ A ∧
      FactorModule (factorRepresentation ρ A) n := by
  cases hcase with
  | natural hm hnatural =>
    cases hnatural with
    | linearTwo F hnatural =>
      obtain ⟨e⟩ := hnatural
      obtain ⟨heq, hdegree⟩ := GroupComparisons.linearTwo hA hAC hn hmodel F e.groupEquiv
      subst C
      refine ⟨hm, .natural F hdegree ?_⟩
      exact composeActionEquiv (commutatorActionEquiv ρ X A hm)
        (composeActionEquiv (fixedQuotientActionEquiv ρ hfix X A) e)
    | symmetricFive hnatural =>
      obtain ⟨e⟩ := hnatural
      obtain ⟨himage, hdegree⟩ := GroupComparisons.symmetricFive hA hAC hn hmodel e.groupEquiv
      subst n
      exact symmetricFive_module ρ hfix X hAC hm e himage
    | linearThree F _ hnatural =>
      obtain ⟨e⟩ := hnatural
      exact (GroupComparisons.not_linearThree hA hAC hmodel F e.groupEquiv).elim
  | doubleNatural F _ _ hnatural =>
    obtain ⟨e⟩ := hnatural
    exact (GroupComparisons.not_linearThree hA hAC hmodel F e.groupEquiv).elim
  | exceptional _ extension =>
    exact (GroupComparisons.not_linearThree hA hAC hmodel BinaryField.two
      extension.natural.groupEquiv).elim

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.MarkedModels
