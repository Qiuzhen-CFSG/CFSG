module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalSubgroups

/-!
# Literal candidate pairs in the two Held local subgroups

The words below were obtained by subgroup exploration in GAP, starting with
the unchanged ATLAS max3/max4 programs. Each word is evaluated in the fixed
Held carrier, in the local generators `a` and `localWord i`. Its membership
in that literal local subgroup is proved by closure induction.

No order, Sylow property, plane identification, or exhaustiveness is asserted
in this module. Those are the remaining certification obligations. In
particular these definitions alone do not classify any pair.

Source: ATLAS HeG1-max3W1 and HeG1-max4W1, preserved in ../source;
GLS3 Table 5.3p. The reproducible exploration and its exact word output are
preserved in source/Explore.g and source/Explore.txt. The existing carrier
inverts GAP permutations, so group-word order is preserved here.
-/

@[expose] public section

namespace Held.LocalPairs.PairCoverage.LocalActions
open Subgroup

/-- Evaluate a word in the literal local generators; false denotes a. -/
def evalLocalWord (i : Bool) (w : List (Bool × ℤ)) : He :=
  (w.map (fun t => (if t.1 then localWord i else a) ^ t.2)).prod

theorem evalLocalWord_mem (i : Bool) (w : List (Bool × ℤ)) :
    evalLocalWord i w ∈ localOvergroup i := by
  induction w with
  | nil => exact (localOvergroup i).one_mem
  | cons t w hw =>
    apply (localOvergroup i).mul_mem _ hw
    apply (localOvergroup i).zpow_mem
    cases t.1
    · exact a_mem_localOvergroup i
    · exact localWord_mem_localOvergroup i

/-- Fixed word data for the odd-subgroup candidates. -/
def oddWord : Bool → Fin 2 → Fin 2 → List (Bool × ℤ)
  | false, 0, 0 =>
    [(true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 6)]
  | false, 0, 1 =>
    [(true, 5), (false, 1), (true, -5), (false, 1)]
  | false, 1, 0 =>
    [(true, -3), (false, 1), (true, -3), (false, 1), (true, 3), (false, 1), (true, -3), (false, 1)]
  | false, 1, 1 =>
    [(true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -5), (false, 1), (true, 1), (false, 1)]
  | true, 0, 0 =>
    [(false, 1), (true, -3), (false, 1), (true, -1), (false, 1), (true, 4), (false, 1), (true, 4)]
  | true, 0, 1 =>
    [(false, 1), (true, 1), (false, 1), (true, 2), (false, 1), (true, -1), (false, 1), (true, 2), (false, 1), (true, 1), (false, 1), (true, 2)]
  | true, 1, 0 =>
    [(true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 4), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1)]
  | true, 1, 1 =>
    [(false, 1), (true, -3), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -4), (false, 1), (true, 2)]

/-- Fixed word data for the two-subgroup candidates. -/
def twoWord : Bool → Fin 2 → Fin 4 → List (Bool × ℤ)
  | false, 0, 0 =>
    [(true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 2), (false, 1), (true, 3), (false, 1), (true, 3)]
  | false, 0, 1 =>
    [(true, -1), (false, 1), (true, -1), (false, 1), (true, 5), (false, 1), (true, -1), (false, 1), (true, -2), (false, 1), (true, 1), (false, 1)]
  | false, 0, 2 =>
    [(true, 2), (false, 1), (true, 1), (false, 1), (true, -3), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 2), (false, 1)]
  | false, 0, 3 =>
    [(false, 1), (true, -2), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1)]
  | false, 1, 0 =>
    [(true, 1), (false, 1), (true, -2), (false, 1), (true, 1), (false, 1), (true, -3), (false, 1), (true, -3), (false, 1)]
  | false, 1, 1 =>
    [(true, 2), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 2), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1)]
  | false, 1, 2 =>
    [(false, 1), (true, -2), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 2), (false, 1), (true, 2), (false, 1), (true, 1), (false, 1)]
  | false, 1, 3 =>
    [(false, 1), (true, -2), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1)]
  | true, 0, 0 =>
    [(true, -4), (false, 1), (true, -4), (false, 1), (true, 1), (false, 1), (true, 2), (false, 1), (true, 1), (false, 1)]
  | true, 0, 1 =>
    [(true, -3), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 2), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1)]
  | true, 0, 2 =>
    [(false, 1), (true, 2), (false, 1), (true, -2), (false, 1), (true, 1), (false, 1), (true, 3), (false, 1), (true, -1), (false, 1)]
  | true, 0, 3 =>
    [(true, 4), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1)]
  | true, 1, 0 =>
    [(true, 4), (false, 1), (true, 3), (false, 1), (true, 3), (false, 1), (true, -1)]
  | true, 1, 1 =>
    [(true, 1), (false, 1), (true, 3), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 3), (false, 1), (true, 1), (false, 1)]
  | true, 1, 2 =>
    [(true, 2), (false, 1), (true, 3), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 3), (false, 1), (true, 1), (false, 1), (true, -1)]
  | true, 1, 3 =>
    [(true, 1), (false, 1), (true, 1), (false, 1), (true, 5), (false, 1), (true, -1), (false, 1), (true, -1)]

/-- Literal odd candidate. Certification of its order is separate. -/
def candidateOdd (i : Bool) (j : Fin 2) : Subgroup He :=
  closure (Set.range (fun k => evalLocalWord i (oddWord i j k)))

/-- Literal two candidate. Certification that it is Sylow is separate. -/
def candidateTwo (i : Bool) (j : Fin 2) : Subgroup He :=
  closure (Set.range (fun k => evalLocalWord i (twoWord i j k)))

theorem candidateOdd_le_localOvergroup (i : Bool) (j : Fin 2) :
    candidateOdd i j ≤ localOvergroup i := by
  apply (closure_le _).mpr
  rintro x ⟨k,rfl⟩
  exact evalLocalWord_mem i _

theorem candidateTwo_le_localOvergroup (i : Bool) (j : Fin 2) :
    candidateTwo i j ≤ localOvergroup i := by
  apply (closure_le _).mpr
  rintro x ⟨k,rfl⟩
  exact evalLocalWord_mem i _

end Held.LocalPairs.PairCoverage.LocalActions
