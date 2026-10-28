module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.Contracts
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.SeedChecks
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.Reduction

/-!
# Left seed factorizations of the marked Sylow subgroup

For each of the 122 literal seeds, every marked Sylow normal form is a seed
member times one of its 32 published representatives. Positive recovery trees
prove membership; checked generator transitions and induction on the normal
form prove coverage. Products retain the left permutation-action convention.

The final application discharges `Reduction.seed_doubleCoset_cover`'s Sylow
factorization premise using the existing eighteen ambient double cosets.
No seed order, coset distinctness, or seed-catalogue exhaustiveness is assumed.
Source: Parrott (1972), section 5, p.683; `ExtensionObstructions/source/README.md`.
-/

namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions

/-- Every marked Sylow normal form has an actual left seed factor. -/
public theorem sylowFactorizations : SylowFactorizations :=
  SylowFactorizationCertificate.covered

/-- The certified factorizations refine the eighteen ambient Sylow double cosets
for the literal seed, representatives, and left multiplication convention. -/
public theorem seed_doubleCoset_cover_certified (i : Fin 122) (x : Atlas1600Group) :
    ∃ (q t : seed i) (a b : Fin 32) (k : Fin 18),
      x = q.val * representative i a b k * t.val :=
  seed_doubleCoset_cover sylowFactorizations i x

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions
