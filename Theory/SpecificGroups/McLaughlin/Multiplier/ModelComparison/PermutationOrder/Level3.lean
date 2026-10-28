module

public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.PermutationOrder.Generators
import Mathlib.Tactic.FinCases

/-!
# McL lower-bound stabilizer level 3

Part of the lower-bound certificate for the literal `McLG1-p275B0` carrier.
The witness generator in `source/` is untrusted; Lean checks every finite
identity. Source permutations and their action convention are in
`Theory/SpecificGroups/LeechRelated/AtlasCarriers/McL.lean`.
-/

@[expose] public section
namespace Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.PermutationOrder
open Theory.GroupTheory Sporadic.LeechRelated.McL
set_option maxRecDepth 100000

namespace Level3

def gen (i : Fin 6) : Equiv.Perm (Fin 275) :=
  match i.val with
  | 0 => p7
  | 1 => p7⁻¹
  | 2 => p8
  | 3 => p8⁻¹
  | 4 => p6
  | _ => p6⁻¹

theorem gen_mem_generated (i : Fin 6) : gen i ∈ generated := by
  fin_cases i
  · exact p7_mem
  · exact generated.inv_mem p7_mem
  · exact p8_mem
  · exact generated.inv_mem p8_mem
  · exact p6_mem
  · exact generated.inv_mem p6_mem

theorem gen_fix : ∀ i : Fin 6, ∀ j : Fin 3,
    gen i ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩ =
      ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩ := by
  apply allFin
  decide +kernel

theorem gen_mem (i : Fin 6) : gen i ∈ stabilizer 3 := by
  refine ⟨gen_mem_generated i, fun j hj => ?_⟩
  exact gen_fix i ⟨j.val, hj⟩

def repWord (i : Fin 36) : List (Fin 6) :=
  match i.val with
  | 0 => []
  | 1 => [0]
  | 2 => [1]
  | 3 => [2]
  | 4 => [4]
  | 5 => [5]
  | 6 => [2, 0]
  | 7 => [3, 0]
  | 8 => [4, 0]
  | 9 => [5, 0]
  | 10 => [4, 1]
  | 11 => [0, 2]
  | 12 => [1, 2]
  | 13 => [4, 2]
  | 14 => [5, 2]
  | 15 => [0, 4]
  | 16 => [1, 4]
  | 17 => [2, 4]
  | 18 => [3, 4]
  | 19 => [4, 4]
  | 20 => [0, 5]
  | 21 => [1, 5]
  | 22 => [0, 2, 0]
  | 23 => [1, 2, 0]
  | 24 => [5, 2, 0]
  | 25 => [0, 3, 0]
  | 26 => [4, 3, 0]
  | 27 => [4, 4, 0]
  | 28 => [1, 5, 0]
  | 29 => [5, 5, 0]
  | 30 => [0, 4, 1]
  | 31 => [1, 4, 1]
  | 32 => [3, 0, 2]
  | 33 => [5, 1, 2]
  | 34 => [4, 0, 4]
  | _ => [5, 0, 4]

def rep (i : Fin 36) : Equiv.Perm (Fin 275) := evalWord gen (repWord i)

/-- A left inverse for the images of the base letter. -/
def imageIndex (x : Fin 275) : Fin 36 :=
  ⟨(4456742057147500101113987851828097211947039795113105068762211074476740506924066183009704907586906138426360103204985502169669886184985291879417926897008640266625077791874921821133681485658267524013035710356224887021570847990395298471351349674248533258322965936187710557932464890045407213083973059075767983235470571918026561138287142023434488639545835943184315835677288893748539165515860720386268279848085709861210699132667824656616415040083398304314567822475376684920261571771955610867231535956063829054320552930388232929634884352188992984216036471611427289250824089694595175137115191197236849354642065242752687375638359491083024444982023069592476370696623374750861046170739446232411385823428472132565361446798195959894109425588240384 >>> (9 * x.val)) % 512 % 36, Nat.mod_lt _ (by decide)⟩

theorem imageIndex_rep : ∀ i, imageIndex (rep i 3) = i := by
  apply allFin
  decide +kernel

theorem card_step : 36 * Nat.card (stabilizer 4) ≤ Nat.card (stabilizer 3) := by
  apply orbit_mul_card_le (k := 3) (by decide) rep
  · intro i
    exact word_mem gen (stabilizer 3) gen_mem (repWord i)
  · exact Function.LeftInverse.injective imageIndex_rep

end Level3
end Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.PermutationOrder
