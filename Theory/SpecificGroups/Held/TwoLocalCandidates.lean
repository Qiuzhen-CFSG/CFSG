module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalSubgroups

/-!
# Three concrete Held two-local candidates

The two existing ATLAS max3/max4 subgroups are the candidates of shape
`2^6:3.S₆`; max5 supplies the candidate of shape `2^(1+6).L₃(2)`.
All three are subgroups of the fixed degree-2058 permutation carrier.
The shapes, normal two-subgroups and exhaustive local coverage remain
separate proof obligations; the definitions assert none of them.

The max5 generators below are the final contents of registers 1 and 2
in the unchanged ATLAS program retained in `TwoLocalCandidates/source`.
The Held generators already invert the GAP permutations, so word order
is preserved when passing from the right action to Lean's left action.

Sources: GLS3 Table 5.3p; ATLAS `HeG1-max3W1`, `HeG1-max4W1`, and
https://brauer.maths.qmul.ac.uk/Atlas/spor/He/words/HeG1-max5W1.
-/

@[expose] public section

namespace Held.TwoLocalCandidates

/-- Register 1 at the end of the ATLAS max5 program. -/
def max5First : He := a * b ^ 3

/-- Register 2 at the end of the ATLAS max5 program. -/
def max5Second : He :=
  let u := max5First ^ 4
  ((u * b⁻¹) * (u * b)) ^ 2 * ((u * b) * (u * b⁻¹)) ^ 2

/-- The literal ATLAS max5 subgroup, without a structure or maximality claim. -/
def max5 : Subgroup He := Subgroup.closure {max5First, max5Second}

/-- The two max3/max4 classes and the max5 candidate, in this order. -/
def subgroup : Fin 3 → Subgroup He
  | 0 => LocalPairs.PairCoverage.localOvergroup false
  | 1 => LocalPairs.PairCoverage.localOvergroup true
  | 2 => max5

theorem max5First_mem : max5First ∈ max5 :=
  Subgroup.subset_closure (Set.mem_insert _ _)

theorem max5Second_mem : max5Second ∈ max5 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

/-- The first candidate generator uses exactly the ambient representation. -/
theorem representation_max5First :
    representation max5First = atlasA * atlasB ^ 3 := by
  simp only [max5First, map_mul, map_pow]
  rfl

/-- The second candidate generator uses exactly the ambient representation. -/
theorem representation_max5Second :
    representation max5Second =
      (((atlasA * atlasB ^ 3) ^ 4 * atlasB⁻¹) *
        ((atlasA * atlasB ^ 3) ^ 4 * atlasB)) ^ 2 *
      (((atlasA * atlasB ^ 3) ^ 4 * atlasB) *
        ((atlasA * atlasB ^ 3) ^ 4 * atlasB⁻¹)) ^ 2 := by
  simp only [max5Second, representation_max5First, map_mul, map_pow, map_inv]
  rfl

/-- The subgroup is identified by its literal generators, not by its order. -/
theorem max5_map :
    max5.map representation =
      Subgroup.closure {representation max5First, representation max5Second} := by
  rw [max5, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton]

end Held.TwoLocalCandidates
