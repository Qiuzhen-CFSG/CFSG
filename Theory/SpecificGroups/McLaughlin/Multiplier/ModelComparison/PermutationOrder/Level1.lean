module

public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.PermutationOrder.Generators
import Mathlib.Tactic.FinCases

/-!
# McL lower-bound stabilizer level 1

Part of the lower-bound certificate for the literal `McLG1-p275B0` carrier.
The witness generator in `source/` is untrusted; Lean checks every finite
identity. Source permutations and their action convention are in
`Theory/SpecificGroups/LeechRelated/AtlasCarriers/McL.lean`.
-/

@[expose] public section
namespace Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.PermutationOrder
open Theory.GroupTheory Sporadic.LeechRelated.McL
set_option maxRecDepth 100000

namespace Level1

def gen (i : Fin 6) : Equiv.Perm (Fin 275) :=
  match i.val with
  | 0 => p2
  | 1 => p2⁻¹
  | 2 => p3
  | 3 => p3⁻¹
  | 4 => p4
  | _ => p4⁻¹

theorem gen_mem_generated (i : Fin 6) : gen i ∈ generated := by
  fin_cases i
  · exact p2_mem
  · exact generated.inv_mem p2_mem
  · exact p3_mem
  · exact generated.inv_mem p3_mem
  · exact p4_mem
  · exact generated.inv_mem p4_mem

theorem gen_fix : ∀ i : Fin 6, ∀ j : Fin 1,
    gen i ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩ =
      ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩ := by
  apply allFin
  decide +kernel

theorem gen_mem (i : Fin 6) : gen i ∈ stabilizer 1 := by
  refine ⟨gen_mem_generated i, fun j hj => ?_⟩
  exact gen_fix i ⟨j.val, hj⟩

def repWord (i : Fin 112) : List (Fin 6) :=
  match i.val with
  | 0 => []
  | 1 => [0]
  | 2 => [1]
  | 3 => [2]
  | 4 => [3]
  | 5 => [0, 0]
  | 6 => [2, 0]
  | 7 => [3, 0]
  | 8 => [4, 0]
  | 9 => [5, 0]
  | 10 => [1, 1]
  | 11 => [2, 1]
  | 12 => [3, 1]
  | 13 => [4, 1]
  | 14 => [5, 1]
  | 15 => [5, 2]
  | 16 => [0, 3]
  | 17 => [3, 3]
  | 18 => [4, 3]
  | 19 => [5, 3]
  | 20 => [0, 0, 0]
  | 21 => [2, 0, 0]
  | 22 => [3, 0, 0]
  | 23 => [4, 0, 0]
  | 24 => [0, 2, 0]
  | 25 => [1, 2, 0]
  | 26 => [2, 2, 0]
  | 27 => [5, 2, 0]
  | 28 => [0, 3, 0]
  | 29 => [1, 3, 0]
  | 30 => [4, 3, 0]
  | 31 => [1, 4, 0]
  | 32 => [4, 4, 0]
  | 33 => [0, 5, 0]
  | 34 => [1, 5, 0]
  | 35 => [2, 5, 0]
  | 36 => [3, 5, 0]
  | 37 => [5, 5, 0]
  | 38 => [1, 1, 1]
  | 39 => [2, 1, 1]
  | 40 => [3, 1, 1]
  | 41 => [4, 1, 1]
  | 42 => [5, 1, 1]
  | 43 => [1, 2, 1]
  | 44 => [1, 3, 1]
  | 45 => [4, 3, 1]
  | 46 => [1, 4, 1]
  | 47 => [3, 4, 1]
  | 48 => [0, 5, 1]
  | 49 => [1, 5, 1]
  | 50 => [3, 5, 1]
  | 51 => [5, 5, 1]
  | 52 => [0, 5, 2]
  | 53 => [1, 5, 2]
  | 54 => [3, 5, 2]
  | 55 => [0, 0, 3]
  | 56 => [3, 0, 3]
  | 57 => [4, 0, 3]
  | 58 => [4, 3, 3]
  | 59 => [0, 4, 3]
  | 60 => [2, 4, 3]
  | 61 => [4, 4, 3]
  | 62 => [0, 5, 3]
  | 63 => [1, 5, 3]
  | 64 => [2, 5, 3]
  | 65 => [0, 0, 0, 0]
  | 66 => [2, 0, 0, 0]
  | 67 => [3, 0, 0, 0]
  | 68 => [1, 2, 0, 0]
  | 69 => [4, 2, 0, 0]
  | 70 => [5, 2, 0, 0]
  | 71 => [0, 3, 0, 0]
  | 72 => [0, 4, 0, 0]
  | 73 => [2, 4, 0, 0]
  | 74 => [3, 4, 0, 0]
  | 75 => [4, 0, 2, 0]
  | 76 => [2, 1, 2, 0]
  | 77 => [3, 1, 2, 0]
  | 78 => [4, 1, 2, 0]
  | 79 => [5, 2, 2, 0]
  | 80 => [5, 5, 2, 0]
  | 81 => [0, 0, 3, 0]
  | 82 => [4, 0, 3, 0]
  | 83 => [5, 0, 3, 0]
  | 84 => [1, 1, 3, 0]
  | 85 => [0, 4, 3, 0]
  | 86 => [1, 4, 3, 0]
  | 87 => [2, 4, 3, 0]
  | 88 => [3, 4, 3, 0]
  | 89 => [2, 1, 4, 0]
  | 90 => [3, 1, 4, 0]
  | 91 => [0, 4, 4, 0]
  | 92 => [0, 0, 5, 0]
  | 93 => [3, 0, 5, 0]
  | 94 => [0, 2, 5, 0]
  | 95 => [2, 5, 5, 0]
  | 96 => [0, 2, 1, 1]
  | 97 => [2, 2, 1, 1]
  | 98 => [5, 3, 1, 1]
  | 99 => [2, 4, 1, 1]
  | 100 => [0, 5, 1, 1]
  | 101 => [5, 1, 2, 1]
  | 102 => [3, 1, 4, 1]
  | 103 => [4, 1, 4, 1]
  | 104 => [1, 3, 4, 1]
  | 105 => [3, 3, 4, 1]
  | 106 => [0, 0, 5, 1]
  | 107 => [4, 0, 5, 1]
  | 108 => [5, 5, 5, 1]
  | 109 => [2, 4, 0, 3]
  | 110 => [4, 0, 3, 0, 0]
  | _ => [4, 3, 1, 2, 0]

def rep (i : Fin 112) : Equiv.Perm (Fin 275) := evalWord gen (repWord i)

/-- A left inverse for the images of the base letter. -/
def imageIndex (x : Fin 275) : Fin 112 :=
  ⟨(1597601539568477830888681706477227363958279194313564446894134998900631580380141488032245640870898517569144777283871687045960598736822796728751007015242398148505905050441427361256152949881884719984364864606163915614879802138404287434261749319528790873532360529516867301287550039720951611682008558563510686865808484855266416277479508808554330949691193506584620118894099036567622871505755415763917567068951868146983718384683910857640034361078871817389014818312707035645016391872332850873113738248186169784485946145182544960592032195666168635861495369983086248441276396830310527217377297088155062483185286406873690275414350496427876913190080354068116865078775283700117330741249822173593049910291236866111096786272964582414270718421783202279468040192 >>> (9 * x.val)) % 512 % 112, Nat.mod_lt _ (by decide)⟩

theorem imageIndex_rep : ∀ i, imageIndex (rep i 1) = i := by
  apply allFin
  decide +kernel

theorem card_step : 112 * Nat.card (stabilizer 2) ≤ Nat.card (stabilizer 1) := by
  apply orbit_mul_card_le (k := 1) (by decide) rep
  · intro i
    exact word_mem gen (stabilizer 1) gen_mem (repWord i)
  · exact Function.LeftInverse.injective imageIndex_rep

end Level1
end Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.PermutationOrder
