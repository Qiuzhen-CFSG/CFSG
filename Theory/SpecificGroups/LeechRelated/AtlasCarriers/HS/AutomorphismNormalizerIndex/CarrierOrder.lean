module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound
import Mathlib.Tactic.FinCases

/-!
# The exact order of the fixed HS permutation carrier

The existing order certificate counts `OrderCertificate.H0`, an overgroup
of the two ATLAS generators. We prove that its nine additional generators
are words in those two generators. All nine permutation equalities are
checked on all 100 letters in Lean's kernel. Thus the overgroup is the
actual carrier, and its certified cardinality is the carrier's cardinality.

Source: GLS3, Table 5.3m, printed p.274; ATLAS HSG1-p100B0, with the
right-to-left action convention of `HS.lean`. Candidate word discovery is
retained in `source/`; GAP's membership answers are not proof premises.
-/

open Theory.GroupTheory
namespace Sporadic.LeechRelated.HS.NormalizerIndex
open OrderCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

private def wordGen (i : Fin 3) : Equiv.Perm (Fin 100) :=
  match i.val with
  | 0 => p0
  | 1 => p1
  | _ => p1⁻¹

private theorem wordGen_mem (i : Fin 3) : wordGen i ∈ generated := by
  have ha : p0 ∈ generated := by
    rw [a_eq_generator]
    exact Subgroup.subset_closure (by simp)
  have hb : p1 ∈ generated := by
    rw [b_eq_generator]
    exact Subgroup.subset_closure (by simp)
  fin_cases i
  · exact ha
  · exact hb
  · exact generated.inv_mem hb

private theorem evalWord_mem (w : List (Fin 3)) : evalWord wordGen w ∈ generated := by
  induction w with
  | nil => exact generated.one_mem
  | cons i w ih => exact generated.mul_mem (wordGen_mem i) ih

private def word2 : List (Fin 3) := [2, 0, 1, 1, 0, 2, 2, 2, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 2, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2]

private theorem word2_eq : evalWord wordGen word2 = p2 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem p2_mem : p2 ∈ generated := word2_eq ▸ evalWord_mem word2

private def word3 : List (Fin 3) := [0, 1, 0, 1, 1, 0, 2, 2, 2, 0, 1, 1, 0, 2, 0]

private theorem word3_eq : evalWord wordGen word3 = p3 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem p3_mem : p3 ∈ generated := word3_eq ▸ evalWord_mem word3

private def word4 : List (Fin 3) := [2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2]

private theorem word4_eq : evalWord wordGen word4 = p4 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem p4_mem : p4 ∈ generated := word4_eq ▸ evalWord_mem word4

private def word5 : List (Fin 3) := [1, 1, 0, 1, 1, 0, 2, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 2, 2, 0, 1, 1, 0]

private theorem word5_eq : evalWord wordGen word5 = p5 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem p5_mem : p5 ∈ generated := word5_eq ▸ evalWord_mem word5

private def word6 : List (Fin 3) := [2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1, 1, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1]

private theorem word6_eq : evalWord wordGen word6 = p6 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem p6_mem : p6 ∈ generated := word6_eq ▸ evalWord_mem word6

private def word7 : List (Fin 3) := [1, 0, 1, 0, 1, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0, 0, 1, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 0, 1, 1, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1]

private theorem word7_eq : evalWord wordGen word7 = p7 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem p7_mem : p7 ∈ generated := word7_eq ▸ evalWord_mem word7

private def word8 : List (Fin 3) := [1, 1, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 1, 1, 0, 2, 0, 2, 2, 0, 1, 1, 0, 1, 0, 2, 2, 2, 2, 0, 2, 0, 2, 0]

private theorem word8_eq : evalWord wordGen word8 = p8 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem p8_mem : p8 ∈ generated := word8_eq ▸ evalWord_mem word8

private def word9 : List (Fin 3) := [2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 1, 1, 0, 1, 0, 1, 0]

private theorem word9_eq : evalWord wordGen word9 = p9 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem p9_mem : p9 ∈ generated := word9_eq ▸ evalWord_mem word9

private def word10 : List (Fin 3) := [0, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 1, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 2, 0, 2, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 2, 2, 0, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1]

private theorem word10_eq : evalWord wordGen word10 = p10 := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem p10_mem : p10 ∈ generated := word10_eq ▸ evalWord_mem word10

private theorem H0_le_generated : H0 ≤ generated := by
  have hgen (i : Fin 20) : gen0 i ∈ generated := by
    have ha : p0 ∈ generated := wordGen_mem 0
    have hb : p1 ∈ generated := wordGen_mem 1
    fin_cases i <;> first
      | exact ha
      | exact hb
      | exact generated.inv_mem hb
      | exact p2_mem
      | exact generated.inv_mem p2_mem
      | exact p3_mem
      | exact generated.inv_mem p3_mem
      | exact p4_mem
      | exact generated.inv_mem p4_mem
      | exact p5_mem
      | exact generated.inv_mem p5_mem
      | exact p6_mem
      | exact generated.inv_mem p6_mem
      | exact p7_mem
      | exact generated.inv_mem p7_mem
      | exact p8_mem
      | exact generated.inv_mem p8_mem
      | exact p9_mem
      | exact generated.inv_mem p9_mem
      | exact p10_mem
      | exact generated.inv_mem p10_mem
  rintro g ⟨w, rfl⟩
  induction w with
  | nil => exact generated.one_mem
  | cons i w ih => exact generated.mul_mem (hgen i) ih

/-- The counted overgroup equals the subgroup of the published generators. -/
public theorem H0_eq_generated : H0 = generated := le_antisymm H0_le_generated generated_le

/-- The exact degree-100 ATLAS carrier has order 44,352,000. -/
public theorem card_carrier : Nat.card Carrier = 44352000 := by
  change Nat.card generated = 44352000
  rw [← H0_eq_generated]
  exact H0_card
end Sporadic.LeechRelated.HS.NormalizerIndex
