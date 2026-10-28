module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.SeedChecks.Block000
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.SeedChecks.Block016
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.SeedChecks.Block032
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.SeedChecks.Block048
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.SeedChecks.Block064
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.SeedChecks.Block080
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.SeedChecks.Block096
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.SeedChecks.Block112

/-!
# All seed factorization certificates

The bounded certificate blocks supply membership and generator closure
for every literal seed, with no remaining certificate premise.

Source: Parrott (1972), section 5, p.683; the candidate JSON in
`ExtensionObstructions/source/`. Reproduce with `source/generate.py`.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizationCertificate

theorem covered (i : Fin 122) (n : Fin 2048) : Covered i (atlas1600SylowTwoNormalForm n) := by
  fin_cases i
  · exact coveredBlock000 0 n
  · exact coveredBlock000 1 n
  · exact coveredBlock000 2 n
  · exact coveredBlock000 3 n
  · exact coveredBlock000 4 n
  · exact coveredBlock000 5 n
  · exact coveredBlock000 6 n
  · exact coveredBlock000 7 n
  · exact coveredBlock000 8 n
  · exact coveredBlock000 9 n
  · exact coveredBlock000 10 n
  · exact coveredBlock000 11 n
  · exact coveredBlock000 12 n
  · exact coveredBlock000 13 n
  · exact coveredBlock000 14 n
  · exact coveredBlock000 15 n
  · exact coveredBlock016 0 n
  · exact coveredBlock016 1 n
  · exact coveredBlock016 2 n
  · exact coveredBlock016 3 n
  · exact coveredBlock016 4 n
  · exact coveredBlock016 5 n
  · exact coveredBlock016 6 n
  · exact coveredBlock016 7 n
  · exact coveredBlock016 8 n
  · exact coveredBlock016 9 n
  · exact coveredBlock016 10 n
  · exact coveredBlock016 11 n
  · exact coveredBlock016 12 n
  · exact coveredBlock016 13 n
  · exact coveredBlock016 14 n
  · exact coveredBlock016 15 n
  · exact coveredBlock032 0 n
  · exact coveredBlock032 1 n
  · exact coveredBlock032 2 n
  · exact coveredBlock032 3 n
  · exact coveredBlock032 4 n
  · exact coveredBlock032 5 n
  · exact coveredBlock032 6 n
  · exact coveredBlock032 7 n
  · exact coveredBlock032 8 n
  · exact coveredBlock032 9 n
  · exact coveredBlock032 10 n
  · exact coveredBlock032 11 n
  · exact coveredBlock032 12 n
  · exact coveredBlock032 13 n
  · exact coveredBlock032 14 n
  · exact coveredBlock032 15 n
  · exact coveredBlock048 0 n
  · exact coveredBlock048 1 n
  · exact coveredBlock048 2 n
  · exact coveredBlock048 3 n
  · exact coveredBlock048 4 n
  · exact coveredBlock048 5 n
  · exact coveredBlock048 6 n
  · exact coveredBlock048 7 n
  · exact coveredBlock048 8 n
  · exact coveredBlock048 9 n
  · exact coveredBlock048 10 n
  · exact coveredBlock048 11 n
  · exact coveredBlock048 12 n
  · exact coveredBlock048 13 n
  · exact coveredBlock048 14 n
  · exact coveredBlock048 15 n
  · exact coveredBlock064 0 n
  · exact coveredBlock064 1 n
  · exact coveredBlock064 2 n
  · exact coveredBlock064 3 n
  · exact coveredBlock064 4 n
  · exact coveredBlock064 5 n
  · exact coveredBlock064 6 n
  · exact coveredBlock064 7 n
  · exact coveredBlock064 8 n
  · exact coveredBlock064 9 n
  · exact coveredBlock064 10 n
  · exact coveredBlock064 11 n
  · exact coveredBlock064 12 n
  · exact coveredBlock064 13 n
  · exact coveredBlock064 14 n
  · exact coveredBlock064 15 n
  · exact coveredBlock080 0 n
  · exact coveredBlock080 1 n
  · exact coveredBlock080 2 n
  · exact coveredBlock080 3 n
  · exact coveredBlock080 4 n
  · exact coveredBlock080 5 n
  · exact coveredBlock080 6 n
  · exact coveredBlock080 7 n
  · exact coveredBlock080 8 n
  · exact coveredBlock080 9 n
  · exact coveredBlock080 10 n
  · exact coveredBlock080 11 n
  · exact coveredBlock080 12 n
  · exact coveredBlock080 13 n
  · exact coveredBlock080 14 n
  · exact coveredBlock080 15 n
  · exact coveredBlock096 0 n
  · exact coveredBlock096 1 n
  · exact coveredBlock096 2 n
  · exact coveredBlock096 3 n
  · exact coveredBlock096 4 n
  · exact coveredBlock096 5 n
  · exact coveredBlock096 6 n
  · exact coveredBlock096 7 n
  · exact coveredBlock096 8 n
  · exact coveredBlock096 9 n
  · exact coveredBlock096 10 n
  · exact coveredBlock096 11 n
  · exact coveredBlock096 12 n
  · exact coveredBlock096 13 n
  · exact coveredBlock096 14 n
  · exact coveredBlock096 15 n
  · exact coveredBlock112 0 n
  · exact coveredBlock112 1 n
  · exact coveredBlock112 2 n
  · exact coveredBlock112 3 n
  · exact coveredBlock112 4 n
  · exact coveredBlock112 5 n
  · exact coveredBlock112 6 n
  · exact coveredBlock112 7 n
  · exact coveredBlock112 8 n
  · exact coveredBlock112 9 n

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizationCertificate
