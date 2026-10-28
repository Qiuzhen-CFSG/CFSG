module

public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.PermutationOrder.Generators
import Mathlib.Tactic.FinCases

/-!
# McL lower-bound stabilizer level 2

Part of the lower-bound certificate for the literal `McLG1-p275B0` carrier.
The witness generator in `source/` is untrusted; Lean checks every finite
identity. Source permutations and their action convention are in
`Theory/SpecificGroups/LeechRelated/AtlasCarriers/McL.lean`.
-/

@[expose] public section
namespace Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.PermutationOrder
open Theory.GroupTheory Sporadic.LeechRelated.McL
set_option maxRecDepth 100000

namespace Level2

def gen (i : Fin 6) : Equiv.Perm (Fin 275) :=
  match i.val with
  | 0 => p4
  | 1 => p4⁻¹
  | 2 => p5
  | 3 => p5⁻¹
  | 4 => p6
  | _ => p6⁻¹

theorem gen_mem_generated (i : Fin 6) : gen i ∈ generated := by
  fin_cases i
  · exact p4_mem
  · exact generated.inv_mem p4_mem
  · exact p5_mem
  · exact generated.inv_mem p5_mem
  · exact p6_mem
  · exact generated.inv_mem p6_mem

theorem gen_fix : ∀ i : Fin 6, ∀ j : Fin 2,
    gen i ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩ =
      ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩ := by
  apply allFin
  decide +kernel

theorem gen_mem (i : Fin 6) : gen i ∈ stabilizer 2 := by
  refine ⟨gen_mem_generated i, fun j hj => ?_⟩
  exact gen_fix i ⟨j.val, hj⟩

def repWord (i : Fin 81) : List (Fin 6) :=
  match i.val with
  | 0 => []
  | 1 => [0]
  | 2 => [1]
  | 3 => [2]
  | 4 => [3]
  | 5 => [0, 0]
  | 6 => [2, 0]
  | 7 => [4, 0]
  | 8 => [5, 0]
  | 9 => [1, 1]
  | 10 => [2, 1]
  | 11 => [3, 1]
  | 12 => [4, 1]
  | 13 => [0, 2]
  | 14 => [1, 2]
  | 15 => [2, 2]
  | 16 => [4, 2]
  | 17 => [5, 2]
  | 18 => [0, 3]
  | 19 => [4, 3]
  | 20 => [5, 3]
  | 21 => [0, 0, 0]
  | 22 => [2, 0, 0]
  | 23 => [3, 0, 0]
  | 24 => [5, 0, 0]
  | 25 => [1, 2, 0]
  | 26 => [5, 2, 0]
  | 27 => [0, 4, 0]
  | 28 => [1, 4, 0]
  | 29 => [2, 4, 0]
  | 30 => [3, 4, 0]
  | 31 => [0, 5, 0]
  | 32 => [1, 5, 0]
  | 33 => [2, 5, 0]
  | 34 => [3, 5, 0]
  | 35 => [4, 1, 1]
  | 36 => [1, 2, 1]
  | 37 => [2, 2, 1]
  | 38 => [4, 2, 1]
  | 39 => [1, 3, 1]
  | 40 => [5, 3, 1]
  | 41 => [1, 4, 1]
  | 42 => [2, 4, 1]
  | 43 => [0, 0, 2]
  | 44 => [2, 0, 2]
  | 45 => [3, 0, 2]
  | 46 => [4, 0, 2]
  | 47 => [5, 0, 2]
  | 48 => [2, 1, 2]
  | 49 => [3, 1, 2]
  | 50 => [5, 1, 2]
  | 51 => [1, 2, 2]
  | 52 => [0, 4, 2]
  | 53 => [1, 4, 2]
  | 54 => [3, 4, 2]
  | 55 => [3, 5, 2]
  | 56 => [3, 0, 3]
  | 57 => [4, 0, 3]
  | 58 => [5, 0, 3]
  | 59 => [1, 4, 3]
  | 60 => [4, 4, 3]
  | 61 => [0, 5, 3]
  | 62 => [0, 0, 0, 0]
  | 63 => [1, 2, 0, 0]
  | 64 => [2, 2, 0, 0]
  | 65 => [4, 3, 0, 0]
  | 66 => [5, 3, 0, 0]
  | 67 => [0, 5, 0, 0]
  | 68 => [2, 5, 2, 0]
  | 69 => [2, 0, 4, 0]
  | 70 => [4, 1, 4, 0]
  | 71 => [5, 2, 4, 0]
  | 72 => [4, 3, 4, 0]
  | 73 => [0, 0, 5, 0]
  | 74 => [3, 1, 5, 0]
  | 75 => [0, 3, 5, 0]
  | 76 => [1, 4, 1, 1]
  | 77 => [4, 1, 3, 1]
  | 78 => [3, 5, 3, 1]
  | 79 => [1, 5, 0, 2]
  | _ => [0, 3, 1, 2]

def rep (i : Fin 81) : Equiv.Perm (Fin 275) := evalWord gen (repWord i)

/-- A left inverse for the images of the base letter. -/
def imageIndex (x : Fin 275) : Fin 81 :=
  ⟨(242687653238052784777449995219099400376349726337104999190337136019882662438023435362219096271452787173749555297396321801053421893680840326451393605358885310960708158721688340928856394684800448948534290873896341205815766101473916222540594716207015251824886169791073249685001339770321077135286933691956275978828856242792018081837066392789104622338825380743223751921050507490108927889962789167172907878270996565121766940685573386024531399694905932576566873910517165344601901450373458051036273966602662564864052373444308800213923990504019967615155073879581461364694744858736695722636597306518125229563278082700772178352849688621558876998134224822338544104255237153436588001086038840196116332692692386243014218518208279877497810946465841382560890880 >>> (9 * x.val)) % 512 % 81, Nat.mod_lt _ (by decide)⟩

theorem imageIndex_rep : ∀ i, imageIndex (rep i 2) = i := by
  apply allFin
  decide +kernel

theorem card_step : 81 * Nat.card (stabilizer 3) ≤ Nat.card (stabilizer 2) := by
  apply orbit_mul_card_le (k := 2) (by decide) rep
  · intro i
    exact word_mem gen (stabilizer 2) gen_mem (repWord i)
  · exact Function.LeftInverse.injective imageIndex_rep

end Level2
end Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.PermutationOrder
