module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.ElementaryCatalogue.Model
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.ElementaryCatalogue.InnerExtensions.Criterion
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.ElementaryCatalogue.InnerExtensions.Checks0
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.ElementaryCatalogue.InnerExtensions.Checks1
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.ElementaryCatalogue.InnerExtensions.Checks2
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.ElementaryCatalogue.InnerExtensions.Checks3
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.ElementaryCatalogue.InnerExtensions.Checks4

/-!
# All inner extensions of the outer Held elementary catalogue

The five node membership lists are certified by binary generator products.
Every one of the 5120 inner extensions either fails a necessary square,
commutation or conjugate-membership test, or passes both inclusions against
one of the five nodes. The conjugation test retains the four inner generators
and the published outer actor; normality is in the full outer stabilizer.

The implication has no realization, quotient bound, coverage or order premise.
It supplies precisely the remaining input to
`normal_elementary_eq_ambientRow_of_inner_extensions` in the parent catalogue.
This module does not assert the source exclusion theorem on its own.
Source: Aschbacher--Smith 15.3.41--42, printed p.1138; GLS3 Table 5.3p;
`Coverage/source/README.md` and `ElementaryCatalogue/source/README.md`.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.CoverageData.ElementaryCatalogue

private theorem inner_branch_checks (i : Option (Fin 4)) (n : Fin 1024) :
    InnerExtensions.branchCheck i n = true := by
  cases i with
  | none => exact InnerExtensions.checked_node0 n
  | some j =>
    fin_cases j
    · exact InnerExtensions.checked_node1 n
    · exact InnerExtensions.checked_node2 n
    · exact InnerExtensions.checked_node3 n
    · exact InnerExtensions.checked_node4 n

/-- Every normal elementary inner extension is exactly one of the five literal nodes.
All finite premises are discharged by kernel-checked permutation certificates. -/
theorem inner_extensions (i : Option (Fin 4)) (n : Fin 1024)
    (hn : (extension i (false, n)).Normal)
    (he : IsElementaryAbelian 2 (extension i (false, n))) :
    ∃ j : Option (Fin 4), extension i (false, n) = node j :=
  ⟨InnerExtensions.target i n,
    InnerExtensions.eq_target_of_check i n (inner_branch_checks i n) hn he⟩

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.CoverageData.ElementaryCatalogue
