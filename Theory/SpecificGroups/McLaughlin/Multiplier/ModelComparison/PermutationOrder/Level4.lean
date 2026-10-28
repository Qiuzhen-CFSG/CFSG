module

public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.PermutationOrder.Generators
import Mathlib.Tactic.FinCases

/-!
# McL lower-bound stabilizer level 4

Part of the lower-bound certificate for the literal `McLG1-p275B0` carrier.
The witness generator in `source/` is untrusted; Lean checks every finite
identity. Source permutations and their action convention are in
`Theory/SpecificGroups/LeechRelated/AtlasCarriers/McL.lean`.
-/

@[expose] public section
namespace Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.PermutationOrder
open Theory.GroupTheory Sporadic.LeechRelated.McL
set_option maxRecDepth 100000

namespace Level4

def gen (i : Fin 4) : Equiv.Perm (Fin 275) :=
  match i.val with
  | 0 => p9
  | 1 => p9⁻¹
  | 2 => p10
  | _ => p10⁻¹

theorem gen_mem_generated (i : Fin 4) : gen i ∈ generated := by
  fin_cases i
  · exact p9_mem
  · exact generated.inv_mem p9_mem
  · exact p10_mem
  · exact generated.inv_mem p10_mem

theorem gen_fix : ∀ i : Fin 4, ∀ j : Fin 4,
    gen i ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩ =
      ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩ := by
  apply allFin
  decide +kernel

theorem gen_mem (i : Fin 4) : gen i ∈ stabilizer 4 := by
  refine ⟨gen_mem_generated i, fun j hj => ?_⟩
  exact gen_fix i ⟨j.val, hj⟩

def repWord (i : Fin 5) : List (Fin 4) :=
  match i.val with
  | 0 => []
  | 1 => [0]
  | 2 => [1]
  | 3 => [0, 0]
  | _ => [1, 1]

def rep (i : Fin 5) : Equiv.Perm (Fin 275) := evalWord gen (repWord i)

/-- A left inverse for the images of the base letter. -/
def imageIndex (x : Fin 275) : Fin 5 :=
  ⟨(25300281663413827294061918339864663381194581227165248389974005609738604953702874167860330207627466496140567074179844857491570007152182766724248956438745494593584721573623632865195419346657905961224034917364554840310934167441919770384267414876653584837511390210143911552365378918215509017799501184083494432069867344251322368 >>> (9 * x.val)) % 512 % 5, Nat.mod_lt _ (by decide)⟩

theorem imageIndex_rep : ∀ i, imageIndex (rep i 4) = i := by
  apply allFin
  decide +kernel

theorem card_step : 5 * Nat.card (stabilizer 5) ≤ Nat.card (stabilizer 4) := by
  apply orbit_mul_card_le (k := 4) (by decide) rep
  · intro i
    exact word_mem gen (stabilizer 4) gen_mem (repWord i)
  · exact Function.LeftInverse.injective imageIndex_rep

end Level4
end Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.PermutationOrder
