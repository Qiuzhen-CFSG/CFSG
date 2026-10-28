module

public import Theory.SpecificGroups.Held.TwoLocalCandidates
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.FinCases

/-!
# Word-defined candidates for the three Held local two-cores

These generators are words in the literal ATLAS max3, max4 and max5
subgroups. The first two lists have six generators, padded by the identity;
the third has seven. The definitions assert no structural facts.
`source/discover.g` records the discovery of these words in the degree-2058
ATLAS representation. Group-word order is unchanged by the conversion
from the right GAP action to the left Lean action.

Source: GLS3, Table 5.3p; ATLAS HeG1-max3W1, max4W1 and max5W1.
-/

@[expose] public section
namespace Held.TwoLocalCandidates.Cores

/-- The two defining elements of each literal candidate. -/
def localGenerator (i : Fin 3) (j : Fin 2) : subgroup i :=
  match i, j with
  | 0, 0 => ⟨a, LocalPairs.PairCoverage.a_mem_localOvergroup false⟩
  | 0, 1 => ⟨LocalPairs.PairCoverage.localWord false,
      LocalPairs.PairCoverage.localWord_mem_localOvergroup false⟩
  | 1, 0 => ⟨a, LocalPairs.PairCoverage.a_mem_localOvergroup true⟩
  | 1, 1 => ⟨LocalPairs.PairCoverage.localWord true,
      LocalPairs.PairCoverage.localWord_mem_localOvergroup true⟩
  | 2, 0 => ⟨max5First, max5First_mem⟩
  | 2, 1 => ⟨max5Second, max5Second_mem⟩

/-- Signed syllables in the two local generators (zero-based indices). -/
def coreWord : Fin 3 → Fin 7 → List (Fin 2 × ℤ)
  | 0, 0 => [(1, 6)]
  | 0, 1 => [(0, 1), (1, 6), (0, -1)]
  | 0, 2 => [(1, 1), (0, 1), (1, 6), (0, -1), (1, -1)]
  | 0, 3 => [(1, 2), (0, 1), (1, 6), (0, -1), (1, -2)]
  | 0, 4 => [(0, 1), (1, 2), (0, 1), (1, 6), (0, -1), (1, -2), (0, -1)]
  | 0, 5 => [(1, 3), (0, 1), (1, 6), (0, -1), (1, -3)]
  | 0, 6 => []
  | 1, 0 => [(1, 5)]
  | 1, 1 => [(0, 1), (1, 5), (0, -1)]
  | 1, 2 => [(1, 1), (0, 1), (1, 5), (0, -1), (1, -1)]
  | 1, 3 => [(0, 1), (1, 1), (0, 1), (1, 5), (0, -1), (1, -1), (0, -1)]
  | 1, 4 => [(1, 1), (0, 1), (1, 1), (0, 1), (1, 5), (0, -1), (1, -1), (0, -1), (1, -1)]
  | 1, 5 => [(1, 2), (0, 1), (1, 1), (0, 1), (1, 5), (0, -1), (1, -1), (0, -1), (1, -2)]
  | 1, 6 => []
  | 2, 0 => [(0, 4)]
  | 2, 1 => [(0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1)]
  | 2, 2 => [(0, 2), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, -1)]
  | 2, 3 => [(1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1)]
  | 2, 4 => [(1, 1), (0, 2), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, -1), (1, -1)]
  | 2, 5 => [(1, 2), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, -1)]
  | 2, 6 => [(1, 2), (0, 2), (1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, -1), (1, -2)]

/-- A core generator, intrinsically in the specified local subgroup. -/
def coreGenerator (i : Fin 3) (j : Fin 7) : subgroup i :=
  ((coreWord i j).map (fun t => localGenerator i t.1 ^ t.2)).prod

/-- The fixed word-defined core candidate; structural assertions are separate proofs. -/
def core (i : Fin 3) : Subgroup (subgroup i) :=
  Subgroup.closure (Set.range (coreGenerator i))

theorem coreGenerator_mem (i : Fin 3) (j : Fin 7) : coreGenerator i j ∈ core i :=
  Subgroup.subset_closure (Set.mem_range_self j)

/-- The faithful permutation representation restricted to a local candidate. -/
def embedding (i : Fin 3) : subgroup i →* Equiv.Perm (Fin 2058) :=
  representation.comp (subgroup i).subtype

theorem embedding_injective (i : Fin 3) : Function.Injective (embedding i) :=
  representation_injective.comp (subgroup i).subtype_injective

theorem localGenerator_closure (i : Fin 3) :
    Subgroup.closure (Set.range (localGenerator i)) = ⊤ := by
  apply Subgroup.map_injective (subgroup i).subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    ← Set.range_comp]
  fin_cases i <;>
    simp only [subgroup, LocalPairs.PairCoverage.localOvergroup, max5] <;>
    congr 1 <;> ext x <;>
    simp [Fin.exists_fin_two, eq_comm] <;> rfl

end Held.TwoLocalCandidates.Cores
