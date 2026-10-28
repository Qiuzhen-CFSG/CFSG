module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.MovedPrime.Cover.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.MovedPrime.Reduction

/-!
# Generation one for moved odd-prime component orbits

Pass through the actual ambient two-core. The faithful component automizer
supplies either a solvable invariant generating cover or genuine minimal
parabolic structure. The selected rows have generation bound one, including
the paired-prime row under its literal minimal-parabolic quotient map.
Generation lifts back through the original two-core. The full Sylow subgroup,
component marking and all SQTK hypotheses of the original contract remain.

Source: Aschbacher--Smith E.1.11--14, E.2.2 and 10.3.3,
printed pp.212--216 and 756--757.
-/

public section
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration
universe u

/-- The exact moved odd-prime component generation contract, without extra premises. -/
theorem movedOddPrimeGeneration : MovedOddPrimeGeneration.{u} :=
  movedOddPrimeGeneration_of_coreFreeCover Cover.coreFreeMovedPrimeCover

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration
