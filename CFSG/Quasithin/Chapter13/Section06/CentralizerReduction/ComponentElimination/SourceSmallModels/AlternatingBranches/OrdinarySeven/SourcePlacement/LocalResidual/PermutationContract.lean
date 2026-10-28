module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.Construction

/-!
# The finite permutation premise in the ordinary A₇ calculation

The even part of the three-pair normalizer normalizes the actual image of Lᵥ,
by 13.6.5 and relative normality in Mᵥ. The finite calculation
places a solvable subgroup of A₇ normalized by this group inside it. Divisibility
by three then forces two-power index. `PermutationLocalStatement` records the
precise finite statement, proved in the sibling `Permutation` module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.6.22, printed p.932 (PDF p.949).
-/

@[expose] public section
open Subgroup Equiv
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.LocalResidual

def evenPairNormalizer : Subgroup (Perm (Fin 7)) :=
  alternatingGroup (Fin 7) ⊓ normalizer (threeTranspositions : Set (Perm (Fin 7)))

/-- The finite permutation prerequisite for the local residual argument.
The sibling `Permutation` module proves this statement. -/
def PermutationLocalStatement : Prop :=
  ∀ D : Subgroup (Perm (Fin 7)), D ≤ alternatingGroup (Fin 7) →
    Group.IsSolvable D → 3 ∣ Nat.card D →
    evenPairNormalizer ≤ normalizer (D : Set (Perm (Fin 7))) →
    D ≤ evenPairNormalizer ∧ ∃ n, D.relIndex evenPairNormalizer = 2 ^ n


end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.LocalResidual
end
