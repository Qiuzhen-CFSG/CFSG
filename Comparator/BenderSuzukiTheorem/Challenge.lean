/-
The Bender-Suzuki theorem: a finite simple group with a strongly embedded subgroup is
`PSL(2, 2ⁿ)`, `Sz(2^(2n+1))` or `PSU(3, 2ⁿ)`.

The statement below, together with `Defs.lean`, is everything a human must audit.  The
public import closure is Mathlib and nothing else, so no declaration of this repository is in the
trusted base.

There are deliberately no entries in `definition_names`.  A definition hole would let a
solution define `IsStronglyEmbedded := fun _ => True` and discharge everything by
`trivial`.
-/
module
public import Comparator.BenderSuzukiTheorem.Defs

universe u

namespace BSTheorem

/-- **The Bender-Suzuki theorem.** -/
public theorem bender_suzuki {X : Type u} [Group X] [Finite X] [IsSimpleGroup X] (M : Subgroup X)
    (hM : IsStronglyEmbedded M) : IsSimpleBenderGroup X := by
  sorry

end BSTheorem
