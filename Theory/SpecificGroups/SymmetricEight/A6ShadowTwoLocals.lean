module

public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.Transport
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.PairStructure
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.FourStructure

/-!
# The C₂ × S₈ overgroups for the A₆ shadow

The concrete pair and four-point block stabilizers are maximal proper
subgroups of characteristic two, generate the whole group, and contain a
common Sylow two-subgroup of order 256. Their two-cores are nontrivial.
The imported permutation calculations establish maximality and the
core-centralizer bounds, and Sylow conjugacy transports this geometry to
every Sylow two-subgroup.

Maximality is stated among proper subgroups: the whole product normalizes
its central C₂, so unrestricted maximal two-local normalizers would include
the whole group.

Source: Aschbacher–Smith, Lemma 2.5.26, printed p.569.
-/

public section

namespace Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
open Subgroup

/-- Every Sylow two-subgroup of C₂ × S₈ lies in two maximal proper
characteristic-two subgroups which generate C₂ × S₈ and have nontrivial
two-cores. The standard pair and four-point block stabilizers supply all
the concrete geometry premises. -/
theorem exists_overgroups (P : Sylow 2 X) :
    ∃ L₁ L₂ : Subgroup X,
      IsCoatom L₁ ∧ IsCoatom L₂ ∧
      (P : Subgroup X) ≤ L₁ ∧ (P : Subgroup X) ≤ L₂ ∧ L₁ ⊔ L₂ = ⊤ ∧
      (L₁ ⊓ centralizer (L₁.pCoreIn 2 : Set X) ≤ L₁.pCoreIn 2) ∧
      (L₂ ⊓ centralizer (L₂.pCoreIn 2 : Set X) ≤ L₂.pCoreIn 2) ∧
      L₁.pCoreIn 2 ≠ ⊥ ∧ L₂.pCoreIn 2 ≠ ⊥ :=
  exists_overgroups_of_standard pairOvergroup_isCoatom fourOvergroup_isCoatom
    pairOvergroup_core_centralizer_le fourOvergroup_core_centralizer_le P

end Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
