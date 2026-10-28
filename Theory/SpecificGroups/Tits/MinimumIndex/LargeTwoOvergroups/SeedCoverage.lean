module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.Seeds
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Root
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Descent
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Checked

/-!
# Exhaustive order-64 seed coverage in the marked Tits Sylow subgroup

Every order-64 subgroup is contained in a chain of five maximal subgroups
starting at the marked group of order 2048. Binary Schreier generators and
831 kernel-checked word certificates conjugate each maximal step onto the
next listed node. Each conjugator belongs to the marked Sylow subgroup.
The final containment is equality because both subgroups then have order 64.
No order or exhaustiveness assertion from the discovery software is assumed.

The last layer is exactly the published `seedIndices`, without reselecting
representatives. The intermediate rows and untrusted witness-discovery code
are saved in `SeedCoverage/source/`.

Source: Parrott (1972), §5, p.683, and the certified 2048 normal forms in
`Atlas1600SylowTwoEnumeration`. The finite subgroup step uses Schreier's lemma
and the maximal-index theorem for finite two-groups.
-/

namespace Tits.MinimumIndex.LargeTwoOvergroups

/-- Every subgroup of order 64 in the marked Sylow subgroup is conjugate,
by an element of that Sylow subgroup, to a published seed. -/
public theorem order64_seed_coverage
    (Q : Subgroup Atlas1600Group) (hle : Q ≤ atlas1600SylowTwoSubgroup)
    (hQ : Nat.card Q = 64) :
    ∃ (i : Fin 122) (s : atlas1600SylowTwoSubgroup),
      Q.map (MulAut.conj s.val).toMonoidHom = seed i :=
  SeedCoverage.coverage_of_steps SeedCoverage.root_eq_top SeedCoverage.all_steps Q hle hQ

end Tits.MinimumIndex.LargeTwoOvergroups
