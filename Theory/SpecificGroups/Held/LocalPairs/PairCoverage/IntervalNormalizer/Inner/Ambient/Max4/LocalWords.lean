module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.Schreier

/-!
# Words for three local normalizer witnesses

For masks 1, 2, and 13, these words in the literal max4 generators give candidate
order-three normalizers. Their conjugation words use the eight original
Schreier generators, numbered one through eight. The membership lemmas use only
word evaluation; the equality and order certificates are proved separately.

Source: unchanged ATLAS max4 and HeG1-p2058B0. `Source/LocalWitnesses.g` records
the untrusted discovery; `Source/local_witnesses.json` retains its output.
-/

@[expose] public section
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4
open Subgroup

/-- The three rows requiring more than the fixed subgroup. -/
def largeRow : Fin 3 → Fin 7 := ![0, 1, 4]

/-- The literal eight Schreier generators for a canonical row. -/
def schreierGenerator (j : Fin 7) (r : Fin 8) : He :=
  indexTwoGenerator (fixedGenerator true) (pivot j) (mask j)
    (decide (4 ≤ r.val)) ⟨r.val % 4, Nat.mod_lt _ (by decide)⟩

theorem schreierGenerator_mem (j : Fin 7) (r : Fin 8) :
    schreierGenerator j r ∈ candidate j := word_mem _ _ _ _

/-- Signed words in the eight Schreier generators. -/
def evalSchreierWord (j : Fin 7) (w : List ℤ) : He :=
  (w.map (fun z =>
    let s := schreierGenerator j ⟨(z.natAbs - 1) % 8, Nat.mod_lt _ (by decide)⟩
    if z < 0 then s⁻¹ else s)).prod

theorem evalSchreierWord_mem (j : Fin 7) (w : List ℤ) :
    evalSchreierWord j w ∈ candidate j := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨z, _, rfl⟩ := List.mem_map.mp hx
  dsimp only
  split
  · exact inv_mem (schreierGenerator_mem j _)
  · exact schreierGenerator_mem j _

/-- Signed words in the two literal max4 generators. -/
def evalMax4Word (w : List ℤ) : He :=
  (w.map (fun k => if k.natAbs = 1 then a ^ k else
    localWord true ^ (if k < 0 then (-1 : ℤ) else 1))).prod

theorem evalMax4Word_mem (w : List ℤ) : evalMax4Word w ∈ localOvergroup true := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
  split
  · exact Subgroup.zpow_mem _ (a_mem_localOvergroup true) _
  · exact Subgroup.zpow_mem _ (localWord_mem_localOvergroup true) _

def localWitnessWord : Fin 3 → List ℤ
  | 0 => [2, 1, -2, 1, -2, -2, -2, -2, 1, -2, -2, 1, 1, -2, 1, 2, 1, 2, 1, 2]
  | 1 => [-2, 1, 2, 1, 2, 1, 2, 2, 1, -2, 1, 2, 1, -2, -1, -2, -1, -2]
  | 2 => [2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, -1, 2, -1, -2, -1, -2, -2, -1, 2, -1, -2]

/-- These are elements of Held, with membership in the literal max4 subgroup. -/
def localWitness (i : Fin 3) : He := evalMax4Word (localWitnessWord i)

theorem localWitness_mem (i : Fin 3) : localWitness i ∈ localOvergroup true :=
  evalMax4Word_mem _

/-- Candidate expressions for conjugated Schreier generators. -/
def conjugateWord : Fin 3 → Fin 8 → List ℤ
  | 0, 0 => []
  | 0, 1 => [-6, -2]
  | 0, 2 => [-3]
  | 0, 3 => [-4, -4, -2, -4, -2]
  | 0, 4 => []
  | 0, 5 => [-2]
  | 0, 6 => [-3]
  | 0, 7 => [-4, -4, 2, 4, 2]
  | 1, 0 => [-3, -5, -3]
  | 1, 1 => []
  | 1, 2 => [-3, -4, -1, -7, -5, -4, -5]
  | 1, 3 => [-3, -4, -4, -4, -8, -1, -7]
  | 1, 4 => [-4, -4, -5, -3, -5]
  | 1, 5 => []
  | 1, 6 => [-4, -4, -1]
  | 1, 7 => [1, 4, 3]
  | 2, 0 => []
  | 2, 1 => [-2]
  | 2, 2 => [-8, -3, 2, 6, 3, -2, -6]
  | 2, 3 => [2, 6, 3, -2, -6]
  | 2, 4 => []
  | 2, 5 => [-6]
  | 2, 6 => [-8, -3, 2, 6, 3, -2, -6]
  | 2, 7 => [-4, -3, 2, 6, 3, -2, -6]

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4
