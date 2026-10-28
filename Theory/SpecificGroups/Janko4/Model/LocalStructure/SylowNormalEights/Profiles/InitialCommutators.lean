module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.Collection

/-!
# First commutators in the three proposed centralizers

These literal identities apply the checked collection procedure to the first
pair in each candidate centralizer sequence. They are initial inputs for the
derived-subgroup calculation, not assertions that those rows generate the full
centralizers or their derived subgroups. The fuel bounds are 136, 258, and 211
adjacent relation rewrites respectively; all three list equalities are checked
by the kernel.

Source: the candidate sequences in `SylowNormalEights/source/profile-data.json`
and the defining power-conjugate relations. The first check took 0.159 seconds
in kernel type checking (the whole import-and-check command used 7.79 seconds
and 2,154,688 KiB peak RSS on 8 October 2026).
-/

public section
open scoped commutatorElement
namespace Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles

/-- A concrete checked application to each of the three candidate centralizers. -/
theorem first_pair_commutator (i : Fin 3) :
    ⁅normalForm ((centralizerMasks i).getD 0 0), normalForm ((centralizerMasks i).getD 1 0)⁆ =
      normalForm (![651336, 1744456, 1744456] i) := by
  fin_cases i
  · exact normalForm_commutator_of_collect 1179937 2 651336 136 (by decide +kernel)
  · exact normalForm_commutator_of_collect 1765409 130 1744456 258 (by decide +kernel)
  · exact normalForm_commutator_of_collect 33 130 1744456 211 (by decide +kernel)

end Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles
