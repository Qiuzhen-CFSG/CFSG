module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.Representatives

/-!
# Independent finite inputs for the seed extension argument

Sylow factorization uses actual members of the literal seed. Representative
witnesses instead concern only fixed elements: either a listed place contains
both the seed and representative, or their extension contains a conjugate of
the ambient Sylow subgroup, an order-25 subgroup, or an order-13 element.
These are independent certificate contracts, not assumptions of the source
result. `Reduction` connects them to the exact single-extension obstruction.

Source: Parrott (1972), section 5, p.683; see `source/README.md`.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions
open Subgroup ExceptionalParabolics

/-- Finite factorizations, without assuming the order of any seed. -/
def SylowFactorizations : Prop :=
  ∀ (i : Fin 122) (n : Fin 2048), ∃ (q : seed i) (a : Fin 32),
    atlas1600SylowTwoNormalForm n = q.val * transversal i a

/-- Explicit group witnesses for one finite representative. -/
def RepresentativeWitness (i : Fin 122) (a b : Fin 32) (k : Fin 18) : Prop :=
  (∃ j ∈ placeIds i, seed i ≤ place j ∧ representative i a b k ∈ place j) ∨
  (∃ g : Atlas1600Group, S.map (MulAut.conj g).toMonoidHom ≤
    singleExtension i (representative i a b k)) ∨
  (∃ L : Subgroup Atlas1600Group, L ≤ singleExtension i (representative i a b k) ∧
    Nat.card L = 25) ∨
  (∃ y : Atlas1600Group, y ∈ singleExtension i (representative i a b k) ∧ orderOf y = 13)

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions
