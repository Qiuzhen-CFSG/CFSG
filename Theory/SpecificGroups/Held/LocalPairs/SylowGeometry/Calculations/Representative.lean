module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Reduction
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalSubgroups

/-!
# A fixed subgroup for the Held Sylow calculations

The four generators are explicit words in the first ATLAS local subgroup
`HeG1-max3W1`, inside the literal degree-2058 Held carrier. GAP selected these
words; their definition makes no claim about their order or Sylow status.
The accompanying source file retains the words independently of GAP's
permutation printer. Lean's Held generators already invert the right-action
ATLAS permutations, so evaluation preserves the original word order.

Source: GLS3 Table 5.3p; ATLAS `HeG1-p2058B0` and `HeG1-max3W1`.
-/

namespace Held.LocalPairs.SylowGeometry.Calculations

/-- Signed words in `a` and the second max3 generator. -/
@[expose] public def generatorWord : Fin 4 → List ℤ
  | 0 => [2, 2, 2, 2, -1, -2, -2, -2, -1, 2, -1, -2, 1, -2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2]
  | 1 => [-1, 2, 2, -1, 2, -1, -2, -1, 2, 2, 2, -1, -2, 1, -2, -2, 1, 2, 2, 2, -1, 2, -1, -2, -2, -1, 2, -1]
  | 2 => [-1, 2, -1, 2, 1, -2, -2, 1, -2, -2, -2, -2, 1, -2, -2, -2, -1, 2, -1, -2, -1, 2]
  | 3 => [-2, -2, -1, -2, -2, -1, 2, 2, 1, 2, 1, -2, -2, 1, 2, 2, 2, 1, 2, 1]

/-- Evaluation in the actual Held carrier, using the max3 local word. -/
@[expose] public def evalLocalWord (w : List ℤ) : He :=
  (w.map (fun k => if k.natAbs = 1 then a ^ k else
    PairCoverage.localWord false ^ (if k < 0 then (-1 : ℤ) else 1))).prod

/-- The chosen four elements, without any unproved recognition of their subgroup. -/
@[expose] public def generator (i : Fin 4) : He := evalLocalWord (generatorWord i)

/-- The concrete subgroup used by the remaining finite checks. -/
@[expose] public def representative : Subgroup He :=
  Subgroup.closure (Set.range generator)

public theorem generator_mem (i : Fin 4) : generator i ∈ representative :=
  Subgroup.subset_closure (Set.mem_range_self i)

public theorem representative_le_localOvergroup :
    representative ≤ PairCoverage.localOvergroup false := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
  split
  · exact Subgroup.zpow_mem _ (PairCoverage.a_mem_localOvergroup false) _
  · exact Subgroup.zpow_mem _ (PairCoverage.localWord_mem_localOvergroup false) _

/-- One kernel-checked moved point suffices for the nontriviality needed below. -/
public theorem generator_one_ne_one : generator 1 ≠ 1 := by
  have hm : representation (generator 1) (0 : Fin 2058) ≠ 0 := by decide +kernel
  intro he
  apply hm
  rw [he, map_one]
  rfl

public theorem representative_ne_bot : representative ≠ ⊥ := by
  intro he
  exact generator_one_ne_one (Subgroup.mem_bot.mp (he ▸ generator_mem 1))

end Held.LocalPairs.SylowGeometry.Calculations
