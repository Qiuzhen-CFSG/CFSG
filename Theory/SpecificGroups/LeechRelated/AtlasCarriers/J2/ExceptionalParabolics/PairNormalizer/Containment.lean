module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Seed
import Mathlib.Tactic.FinCases

/-!
# Placement of the second Hall--Janko radical candidate

Each of the six fixed generators of `Seed.q₂` is a short word in the inverses
of the seven fixed generators of `Seed.s`. These identities prove the literal
containment in the degree-100 ATLAS carrier. They are checked against the
published generator tables, without changing either seed subgroup.

The short words were found by GAP from the retained ATLAS words in
`ExceptionalParabolics/source/seed.json`; GAP supplies witnesses only.
Source: GLS3, Table 5.3g, and Aschbacher--Smith, printed p.511 (PDF p.528).
-/

@[expose] public section

namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer
open Theory.GroupTheory GeneratorPair Seed

private theorem inclusion_localWord (w : List (Fin 3)) :
    inclusion (localWord w) = evalWord ![tableA, tableB, tableB⁻¹] w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change inclusion (![a, b, b⁻¹] i * localWord w) = _
    rw [map_mul, ih]
    congr 1
    fin_cases i <;> simp [a, b, inclusion, generatorA_eq_table, generatorB_eq_table]

/-- Words in the inverse Sylow-candidate generators representing the radical generators. -/
def q₂InSWords : Fin 6 → List (Fin 7) := ![[2], [1], [4, 0], [0], [5, 3, 0, 4], [6]]

private theorem inclusion_inverse_sWord (w : List (Fin 7)) :
    inclusion (evalWord (fun i => (sGenerator i)⁻¹) w) =
      evalWord (fun i => (evalWord ![tableA, tableB, tableB⁻¹] (sWords i))⁻¹) w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change inclusion ((sGenerator i)⁻¹ * evalWord _ w) = _
    rw [map_mul, map_inv, ih]
    exact congrArg (fun x => x⁻¹ * _) (inclusion_localWord (sWords i))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Exact word witnesses for the placement of all six radical generators. -/
theorem q₂Generator_eq_sWord (i : Fin 6) :
    q₂Generator i = evalWord (fun j => (sGenerator j)⁻¹) (q₂InSWords i) := by
  apply inclusion_injective
  rw [inclusion_inverse_sWord]
  change inclusion (localWord (q₂Words i)) = _
  rw [inclusion_localWord]
  fin_cases i <;> decide +kernel

/-- The radical candidate is contained in the fixed Sylow candidate. -/
theorem q₂_le_s : q₂ ≤ s := by
  apply (Subgroup.closure_le s).mpr
  rintro _ ⟨i, rfl⟩
  rw [q₂Generator_eq_sWord]
  generalize q₂InSWords i = w
  induction w with
  | nil => exact s.one_mem
  | cons j w ih =>
    exact s.mul_mem (s.inv_mem (Subgroup.subset_closure ⟨j, rfl⟩)) ih

end Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer
