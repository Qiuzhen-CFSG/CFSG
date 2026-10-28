module

public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.PermutationOrder.Generators
import Mathlib.Tactic.FinCases

/-!
# McL lower-bound stabilizer level 5

Part of the lower-bound certificate for the literal `McLG1-p275B0` carrier.
The witness generator in `source/` is untrusted; Lean checks every finite
identity. Source permutations and their action convention are in
`Theory/SpecificGroups/LeechRelated/AtlasCarriers/McL.lean`.
-/

@[expose] public section
namespace Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.PermutationOrder
open Theory.GroupTheory Sporadic.LeechRelated.McL
set_option maxRecDepth 100000

namespace Level5

def gen (i : Fin 2) : Equiv.Perm (Fin 275) :=
  match i.val with
  | 0 => p10
  | _ => p10⁻¹

theorem gen_mem_generated (i : Fin 2) : gen i ∈ generated := by
  fin_cases i
  · exact p10_mem
  · exact generated.inv_mem p10_mem

theorem gen_fix : ∀ i : Fin 2, ∀ j : Fin 5,
    gen i ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩ =
      ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩ := by
  apply allFin
  decide +kernel

theorem gen_mem (i : Fin 2) : gen i ∈ stabilizer 5 := by
  refine ⟨gen_mem_generated i, fun j hj => ?_⟩
  exact gen_fix i ⟨j.val, hj⟩

def repWord (i : Fin 2) : List (Fin 2) :=
  match i.val with
  | 0 => []
  | _ => [0]

def rep (i : Fin 2) : Equiv.Perm (Fin 275) := evalWord gen (repWord i)

/-- A left inverse for the images of the base letter. -/
def imageIndex (x : Fin 275) : Fin 2 :=
  ⟨(3112014485284098585574436493586758696655010877757361905428101737040614728882455638019466441795865969169955187863977325342919189349926788113175446764975532607962725174097746256800873673380257967140261374620443337755114242316111687243965260952844956826571551652997073766550583935587323971626310125466127826352612655019251188242482944902109991778966894206864829352119744939820210298992902804543092908565237163768564305060181632481080346503458423209317409980850660845585113649673280863970422292395633540137202288546311652523962496312218878761517509124115362543979875181569915082262970368 >>> (9 * x.val)) % 512 % 2, Nat.mod_lt _ (by decide)⟩

theorem imageIndex_rep : ∀ i, imageIndex (rep i 5) = i := by
  apply allFin
  decide +kernel

theorem card_step : 2 * Nat.card (stabilizer 6) ≤ Nat.card (stabilizer 5) := by
  apply orbit_mul_card_le (k := 5) (by decide) rep
  · intro i
    exact word_mem gen (stabilizer 5) gen_mem (repWord i)
  · exact Function.LeftInverse.injective imageIndex_rep

end Level5
end Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.PermutationOrder
