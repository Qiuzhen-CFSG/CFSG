module

public import Theory.SpecificGroups.Held.Model.RelatorChecks

/-!
# Exact orders of the Held standard generators

The checked relators give powers 2, 7, 17 equal to one. Each permutation
moves point zero, so primality proves its order is exactly the stated prime.
The expensive full permutation checks live in `RelatorChecks`.
-/

namespace Held

public theorem atlasA_sq : atlasA ^ 2 = 1 := atlas_relations 0

public theorem atlasB_pow_seven : atlasB ^ 7 = 1 := atlas_relations 1

public theorem atlasAB_pow_seventeen : (atlasA * atlasB) ^ 17 = 1 := atlas_relations 2

public theorem atlasA_ne_one : atlasA ≠ 1 := by
  have hmove : atlasA (0 : Fin 2058) ≠ 0 := by decide +kernel
  exact fun h => hmove (congrArg (fun p : Equiv.Perm (Fin 2058) => p 0) h)

public theorem atlasB_ne_one : atlasB ≠ 1 := by
  have hmove : atlasB (0 : Fin 2058) ≠ 0 := by decide +kernel
  exact fun h => hmove (congrArg (fun p : Equiv.Perm (Fin 2058) => p 0) h)

public theorem atlasAB_ne_one : atlasA * atlasB ≠ 1 := by
  have hmove : (atlasA * atlasB) (0 : Fin 2058) ≠ 0 := by decide +kernel
  exact fun h => hmove (congrArg (fun p : Equiv.Perm (Fin 2058) => p 0) h)

public theorem orderOf_atlasA : orderOf atlasA = 2 :=
  orderOf_eq_prime atlasA_sq atlasA_ne_one

public theorem orderOf_atlasB : orderOf atlasB = 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact orderOf_eq_prime atlasB_pow_seven atlasB_ne_one

public theorem orderOf_atlasAB : orderOf (atlasA * atlasB) = 17 := by
  let : Fact (Nat.Prime 17) := ⟨by decide⟩
  exact orderOf_eq_prime atlasAB_pow_seventeen atlasAB_ne_one

end Held
