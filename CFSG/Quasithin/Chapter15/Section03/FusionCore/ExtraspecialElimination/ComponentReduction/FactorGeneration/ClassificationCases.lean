module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationPreparation
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.SymmetricThree

/-!
# Local factors from the FF-module alternatives

SaturatedLift constructs the canonical factor above a specified subgroup of
J* = ⟨A^H⟩* and proves its kernel saturation and relative subnormality.
SymmetricThree derives the cubic commutator identity and constructs the
complete solvable candidate in B.5.6(2), on the actual SectionAction.
ClassificationPreparation supplies the B.5.3 hypotheses for that action.
The selected nontrivial offender also excludes the trivial actor allowed
by B.5.3.

The exhaustive local reduction remains unfinished: the outer automorphism
alternatives, the two-factor cases (including exceptional module extensions),
and lifting component generation through the solvable kernel still require
proof. In particular these exports do not assert 15.3.49(i), nor do they
postulate that failure of component generation supplies an S₃ factor.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.99–110 and 1143–1144. Final case assembly belongs to this module;
the source (i)–(j) assembly belongs to FactorGeneration.
-/

public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases

variable {G : Type*} [Group G]

/-- The actual selected offender excludes the trivial B.5.3 actor. -/
theorem starSpan_nontrivial_of_bestOffender
    (H ZS Z A : Subgroup G) [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hbest : IsBestOffender action.representation (starImage H A)) :
    Nontrivial (starImage H (localSpan A H)) := by
  apply (Subgroup.nontrivial_iff_ne_bot _).mpr
  intro hbot
  exact hbest.1.1 (le_bot_iff.mp
    ((map_mono (comap_mono (le_conjugateSpanBy A H))).trans_eq hbot))

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases
