module
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart.Coordinates
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart.Support
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart.BlockAction

/-!
# Negative short-root coordinates

For each of the two negative elementary SL3 generators, the sparse block
formulas agree with the checked supports of the negative F4 divided powers.
The finite coordinate calculation uses symmetry of the six symmetric blocks
and cancellation of the repeated linear term in characteristic two.
The Cartan coordinates are checked separately using their diagonal sums.

Source: GLS3 §2.6.2, the short A₂ lattice. These are symbolic identities over
an arbitrary field of characteristic two, not tests at finitely many parameters.
-/

namespace ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart
open TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.ShortA2
open SourceBlocks Coefficients BlockAction
variable (F : Type*) [Field F] [CharP F 2]
-- A uniform finite-row proof template intentionally contains redundant branches.
set_option linter.unusedSimpArgs false

set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

private theorem root_0_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 0) =
      toCoords F v (.inr 0) + t * ∑ c ∈ rowSupport false false 0 (.inr 0), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 0), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 0) = ∅ from rfl,
    show rowSupport false false 1 (.inr 0) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change (action F (modelGenerator F false false t) v).2.1 1 = (v.2.1 1)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_0_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 0) =
      toCoords F v (.inr 0) + t * ∑ c ∈ rowSupport false true 0 (.inr 0), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 0), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 0) = ∅ from rfl,
    show rowSupport false true 1 (.inr 0) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change (action F (modelGenerator F false true t) v).2.1 1 = (v.2.1 1)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_1_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 1) =
      toCoords F v (.inr 1) + t * ∑ c ∈ rowSupport false false 0 (.inr 1), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 1), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 1) = ∅ from rfl,
    show rowSupport false false 1 (.inr 1) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change (action F (modelGenerator F false false t) v).2.1 2 = (v.2.1 2)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_1_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 1) =
      toCoords F v (.inr 1) + t * ∑ c ∈ rowSupport false true 0 (.inr 1), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 1), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 1) = ∅ from rfl,
    show rowSupport false true 1 (.inr 1) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change (action F (modelGenerator F false true t) v).2.1 2 = (v.2.1 2)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_2_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 2) =
      toCoords F v (.inr 2) + t * ∑ c ∈ rowSupport false false 0 (.inr 2), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 2), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 2) = ∅ from rfl,
    show rowSupport false false 1 (.inr 2) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.2 0).val 0 0 = ((v.2.2.2 0).val 0 0)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_2_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 2) =
      toCoords F v (.inr 2) + t * ∑ c ∈ rowSupport false true 0 (.inr 2), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 2), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 2) = ∅ from rfl,
    show rowSupport false true 1 (.inr 2) = {Sum.inr 4} from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.2 0).val 0 0 = ((v.2.2.2 0).val 0 0) + t ^ 2 * (((v.2.2.2 0).val 1 1))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_3_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 3) =
      toCoords F v (.inr 3) + t * ∑ c ∈ rowSupport false false 0 (.inr 3), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 3), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 3) = {Sum.inr 7} from rfl,
    show rowSupport false false 1 (.inr 3) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.2 0).val 0 1 = ((v.2.2.2 0).val 0 1) + t * (((v.2.2.2 0).val 0 2))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_3_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 3) =
      toCoords F v (.inr 3) + t * ∑ c ∈ rowSupport false true 0 (.inr 3), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 3), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 3) = {Sum.inr 4} from rfl,
    show rowSupport false true 1 (.inr 3) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.2 0).val 0 1 = ((v.2.2.2 0).val 0 1) + t * (((v.2.2.2 0).val 1 1))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_4_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 4) =
      toCoords F v (.inr 4) + t * ∑ c ∈ rowSupport false false 0 (.inr 4), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 4), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 4) = ∅ from rfl,
    show rowSupport false false 1 (.inr 4) = {Sum.inr 15} from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.2 0).val 1 1 = ((v.2.2.2 0).val 1 1) + t ^ 2 * (((v.2.2.2 0).val 2 2))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_4_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 4) =
      toCoords F v (.inr 4) + t * ∑ c ∈ rowSupport false true 0 (.inr 4), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 4), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 4) = ∅ from rfl,
    show rowSupport false true 1 (.inr 4) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.2 0).val 1 1 = ((v.2.2.2 0).val 1 1)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_5_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 5) =
      toCoords F v (.inr 5) + t * ∑ c ∈ rowSupport false false 0 (.inr 5), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 5), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 5) = ∅ from rfl,
    show rowSupport false false 1 (.inr 5) = {Sum.inr 16} from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.1 0).val 2 2 = ((v.2.2.1 0).val 2 2) + t ^ 2 * (((v.2.2.1 0).val 1 1))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_5_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 5) =
      toCoords F v (.inr 5) + t * ∑ c ∈ rowSupport false true 0 (.inr 5), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 5), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 5) = ∅ from rfl,
    show rowSupport false true 1 (.inr 5) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.1 0).val 2 2 = ((v.2.2.1 0).val 2 2)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_6_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 6) =
      toCoords F v (.inr 6) + t * ∑ c ∈ rowSupport false false 0 (.inr 6), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 6), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 6) = ∅ from rfl,
    show rowSupport false false 1 (.inr 6) = {Sum.inr 20} from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.1 1).val 2 2 = ((v.2.2.1 1).val 2 2) + t ^ 2 * (((v.2.2.1 1).val 1 1))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_6_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 6) =
      toCoords F v (.inr 6) + t * ∑ c ∈ rowSupport false true 0 (.inr 6), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 6), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 6) = ∅ from rfl,
    show rowSupport false true 1 (.inr 6) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.1 1).val 2 2 = ((v.2.2.1 1).val 2 2)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_7_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 7) =
      toCoords F v (.inr 7) + t * ∑ c ∈ rowSupport false false 0 (.inr 7), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 7), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 7) = ∅ from rfl,
    show rowSupport false false 1 (.inr 7) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.2 0).val 0 2 = ((v.2.2.2 0).val 0 2)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_7_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 7) =
      toCoords F v (.inr 7) + t * ∑ c ∈ rowSupport false true 0 (.inr 7), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 7), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 7) = {Sum.inr 8} from rfl,
    show rowSupport false true 1 (.inr 7) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.2 0).val 0 2 = ((v.2.2.2 0).val 0 2) + t * (((v.2.2.2 0).val 1 2))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_8_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 8) =
      toCoords F v (.inr 8) + t * ∑ c ∈ rowSupport false false 0 (.inr 8), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 8), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 8) = {Sum.inr 15} from rfl,
    show rowSupport false false 1 (.inr 8) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.2 0).val 1 2 = ((v.2.2.2 0).val 1 2) + t * (((v.2.2.2 0).val 2 2))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_8_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 8) =
      toCoords F v (.inr 8) + t * ∑ c ∈ rowSupport false true 0 (.inr 8), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 8), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 8) = ∅ from rfl,
    show rowSupport false true 1 (.inr 8) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.2 0).val 1 2 = ((v.2.2.2 0).val 1 2)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_9_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 9) =
      toCoords F v (.inr 9) + t * ∑ c ∈ rowSupport false false 0 (.inr 9), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 9), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 9) = {Sum.inr 16} from rfl,
    show rowSupport false false 1 (.inr 9) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.1 0).val 1 2 = ((v.2.2.1 0).val 1 2) + t * (((v.2.2.1 0).val 1 1))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_9_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 9) =
      toCoords F v (.inr 9) + t * ∑ c ∈ rowSupport false true 0 (.inr 9), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 9), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 9) = {Sum.inr 10} from rfl,
    show rowSupport false true 1 (.inr 9) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.1 0).val 1 2 = ((v.2.2.1 0).val 1 2) + t * (((v.2.2.1 0).val 0 2))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_10_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 10) =
      toCoords F v (.inr 10) + t * ∑ c ∈ rowSupport false false 0 (.inr 10), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 10), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 10) = {Sum.inr 17} from rfl,
    show rowSupport false false 1 (.inr 10) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.1 0).val 0 2 = ((v.2.2.1 0).val 0 2) + t * (((v.2.2.1 0).val 0 1))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_10_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 10) =
      toCoords F v (.inr 10) + t * ∑ c ∈ rowSupport false true 0 (.inr 10), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 10), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 10) = ∅ from rfl,
    show rowSupport false true 1 (.inr 10) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.1 0).val 0 2 = ((v.2.2.1 0).val 0 2)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_11_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 11) =
      toCoords F v (.inr 11) + t * ∑ c ∈ rowSupport false false 0 (.inr 11), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 11), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 11) = {Sum.inr 20} from rfl,
    show rowSupport false false 1 (.inr 11) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.1 1).val 1 2 = ((v.2.2.1 1).val 1 2) + t * (((v.2.2.1 1).val 1 1))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_11_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 11) =
      toCoords F v (.inr 11) + t * ∑ c ∈ rowSupport false true 0 (.inr 11), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 11), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 11) = {Sum.inr 12} from rfl,
    show rowSupport false true 1 (.inr 11) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.1 1).val 1 2 = ((v.2.2.1 1).val 1 2) + t * (((v.2.2.1 1).val 0 2))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_12_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 12) =
      toCoords F v (.inr 12) + t * ∑ c ∈ rowSupport false false 0 (.inr 12), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 12), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 12) = {Sum.inr 21} from rfl,
    show rowSupport false false 1 (.inr 12) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.1 1).val 0 2 = ((v.2.2.1 1).val 0 2) + t * (((v.2.2.1 1).val 0 1))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_12_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 12) =
      toCoords F v (.inr 12) + t * ∑ c ∈ rowSupport false true 0 (.inr 12), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 12), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 12) = ∅ from rfl,
    show rowSupport false true 1 (.inr 12) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.1 1).val 0 2 = ((v.2.2.1 1).val 0 2)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_13_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 13) =
      toCoords F v (.inr 13) + t * ∑ c ∈ rowSupport false false 0 (.inr 13), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 13), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 13) = {Sum.inr 23} from rfl,
    show rowSupport false false 1 (.inr 13) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change (action F (modelGenerator F false false t) v).1 2 0 = (v.1 2 0) + t * ((v.1 1 0))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_13_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 13) =
      toCoords F v (.inr 13) + t * ∑ c ∈ rowSupport false true 0 (.inr 13), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 13), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 13) = {Sum.inr 14} from rfl,
    show rowSupport false true 1 (.inr 13) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change (action F (modelGenerator F false true t) v).1 2 0 = (v.1 2 0) + t * ((v.1 2 1))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_14_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 14) =
      toCoords F v (.inr 14) + t * ∑ c ∈ rowSupport false false 0 (.inr 14), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 14), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 14) = {Sum.inl 2} from rfl,
    show rowSupport false false 1 (.inr 14) = {Sum.inr 33} from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change (action F (modelGenerator F false false t) v).1 2 1 = (v.1 2 1) + t * ((v.1 1 1 + v.1 2 2)) + t ^ 2 * ((v.1 1 2))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_14_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 14) =
      toCoords F v (.inr 14) + t * ∑ c ∈ rowSupport false true 0 (.inr 14), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 14), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 14) = ∅ from rfl,
    show rowSupport false true 1 (.inr 14) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change (action F (modelGenerator F false true t) v).1 2 1 = (v.1 2 1)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_15_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 15) =
      toCoords F v (.inr 15) + t * ∑ c ∈ rowSupport false false 0 (.inr 15), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 15), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 15) = ∅ from rfl,
    show rowSupport false false 1 (.inr 15) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.2 0).val 2 2 = ((v.2.2.2 0).val 2 2)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_15_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 15) =
      toCoords F v (.inr 15) + t * ∑ c ∈ rowSupport false true 0 (.inr 15), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 15), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 15) = ∅ from rfl,
    show rowSupport false true 1 (.inr 15) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.2 0).val 2 2 = ((v.2.2.2 0).val 2 2)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_16_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 16) =
      toCoords F v (.inr 16) + t * ∑ c ∈ rowSupport false false 0 (.inr 16), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 16), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 16) = ∅ from rfl,
    show rowSupport false false 1 (.inr 16) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.1 0).val 1 1 = ((v.2.2.1 0).val 1 1)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_16_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 16) =
      toCoords F v (.inr 16) + t * ∑ c ∈ rowSupport false true 0 (.inr 16), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 16), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 16) = ∅ from rfl,
    show rowSupport false true 1 (.inr 16) = {Sum.inr 18} from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.1 0).val 1 1 = ((v.2.2.1 0).val 1 1) + t ^ 2 * (((v.2.2.1 0).val 0 0))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_17_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 17) =
      toCoords F v (.inr 17) + t * ∑ c ∈ rowSupport false false 0 (.inr 17), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 17), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 17) = ∅ from rfl,
    show rowSupport false false 1 (.inr 17) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.1 0).val 0 1 = ((v.2.2.1 0).val 0 1)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_17_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 17) =
      toCoords F v (.inr 17) + t * ∑ c ∈ rowSupport false true 0 (.inr 17), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 17), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 17) = {Sum.inr 18} from rfl,
    show rowSupport false true 1 (.inr 17) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.1 0).val 0 1 = ((v.2.2.1 0).val 0 1) + t * (((v.2.2.1 0).val 0 0))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_18_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 18) =
      toCoords F v (.inr 18) + t * ∑ c ∈ rowSupport false false 0 (.inr 18), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 18), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 18) = ∅ from rfl,
    show rowSupport false false 1 (.inr 18) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.1 0).val 0 0 = ((v.2.2.1 0).val 0 0)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_18_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 18) =
      toCoords F v (.inr 18) + t * ∑ c ∈ rowSupport false true 0 (.inr 18), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 18), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 18) = ∅ from rfl,
    show rowSupport false true 1 (.inr 18) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.1 0).val 0 0 = ((v.2.2.1 0).val 0 0)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_19_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 19) =
      toCoords F v (.inr 19) + t * ∑ c ∈ rowSupport false false 0 (.inr 19), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 19), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 19) = ∅ from rfl,
    show rowSupport false false 1 (.inr 19) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change (action F (modelGenerator F false false t) v).2.1 3 = (v.2.1 3)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_19_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 19) =
      toCoords F v (.inr 19) + t * ∑ c ∈ rowSupport false true 0 (.inr 19), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 19), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 19) = ∅ from rfl,
    show rowSupport false true 1 (.inr 19) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change (action F (modelGenerator F false true t) v).2.1 3 = (v.2.1 3)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_20_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 20) =
      toCoords F v (.inr 20) + t * ∑ c ∈ rowSupport false false 0 (.inr 20), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 20), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 20) = ∅ from rfl,
    show rowSupport false false 1 (.inr 20) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.1 1).val 1 1 = ((v.2.2.1 1).val 1 1)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_20_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 20) =
      toCoords F v (.inr 20) + t * ∑ c ∈ rowSupport false true 0 (.inr 20), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 20), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 20) = ∅ from rfl,
    show rowSupport false true 1 (.inr 20) = {Sum.inr 22} from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.1 1).val 1 1 = ((v.2.2.1 1).val 1 1) + t ^ 2 * (((v.2.2.1 1).val 0 0))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_21_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 21) =
      toCoords F v (.inr 21) + t * ∑ c ∈ rowSupport false false 0 (.inr 21), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 21), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 21) = ∅ from rfl,
    show rowSupport false false 1 (.inr 21) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.1 1).val 0 1 = ((v.2.2.1 1).val 0 1)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_21_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 21) =
      toCoords F v (.inr 21) + t * ∑ c ∈ rowSupport false true 0 (.inr 21), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 21), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 21) = {Sum.inr 22} from rfl,
    show rowSupport false true 1 (.inr 21) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.1 1).val 0 1 = ((v.2.2.1 1).val 0 1) + t * (((v.2.2.1 1).val 0 0))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_22_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 22) =
      toCoords F v (.inr 22) + t * ∑ c ∈ rowSupport false false 0 (.inr 22), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 22), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 22) = ∅ from rfl,
    show rowSupport false false 1 (.inr 22) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.1 1).val 0 0 = ((v.2.2.1 1).val 0 0)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_22_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 22) =
      toCoords F v (.inr 22) + t * ∑ c ∈ rowSupport false true 0 (.inr 22), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 22), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 22) = ∅ from rfl,
    show rowSupport false true 1 (.inr 22) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.1 1).val 0 0 = ((v.2.2.1 1).val 0 0)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_23_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 23) =
      toCoords F v (.inr 23) + t * ∑ c ∈ rowSupport false false 0 (.inr 23), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 23), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 23) = ∅ from rfl,
    show rowSupport false false 1 (.inr 23) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change (action F (modelGenerator F false false t) v).1 1 0 = (v.1 1 0)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_23_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 23) =
      toCoords F v (.inr 23) + t * ∑ c ∈ rowSupport false true 0 (.inr 23), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 23), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 23) = {Sum.inl 1, Sum.inl 3} from rfl,
    show rowSupport false true 1 (.inr 23) = {Sum.inr 24} from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change (action F (modelGenerator F false true t) v).1 1 0 = (v.1 1 0) + t * ((v.2.1 0) + (v.1 0 0 + v.1 1 1 + v.2.1 0)) + t ^ 2 * ((v.1 0 1))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_24_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 24) =
      toCoords F v (.inr 24) + t * ∑ c ∈ rowSupport false false 0 (.inr 24), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 24), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 24) = {Sum.inr 34} from rfl,
    show rowSupport false false 1 (.inr 24) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change (action F (modelGenerator F false false t) v).1 0 1 = (v.1 0 1) + t * ((v.1 0 2))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_24_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 24) =
      toCoords F v (.inr 24) + t * ∑ c ∈ rowSupport false true 0 (.inr 24), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 24), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 24) = ∅ from rfl,
    show rowSupport false true 1 (.inr 24) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change (action F (modelGenerator F false true t) v).1 0 1 = (v.1 0 1)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_25_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 25) =
      toCoords F v (.inr 25) + t * ∑ c ∈ rowSupport false false 0 (.inr 25), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 25), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 25) = ∅ from rfl,
    show rowSupport false false 1 (.inr 25) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.2 1).val 0 0 = ((v.2.2.2 1).val 0 0)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_25_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 25) =
      toCoords F v (.inr 25) + t * ∑ c ∈ rowSupport false true 0 (.inr 25), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 25), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 25) = ∅ from rfl,
    show rowSupport false true 1 (.inr 25) = {Sum.inr 27} from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.2 1).val 0 0 = ((v.2.2.2 1).val 0 0) + t ^ 2 * (((v.2.2.2 1).val 1 1))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_26_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 26) =
      toCoords F v (.inr 26) + t * ∑ c ∈ rowSupport false false 0 (.inr 26), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 26), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 26) = {Sum.inr 35} from rfl,
    show rowSupport false false 1 (.inr 26) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.2 1).val 0 1 = ((v.2.2.2 1).val 0 1) + t * (((v.2.2.2 1).val 0 2))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_26_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 26) =
      toCoords F v (.inr 26) + t * ∑ c ∈ rowSupport false true 0 (.inr 26), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 26), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 26) = {Sum.inr 27} from rfl,
    show rowSupport false true 1 (.inr 26) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.2 1).val 0 1 = ((v.2.2.2 1).val 0 1) + t * (((v.2.2.2 1).val 1 1))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_27_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 27) =
      toCoords F v (.inr 27) + t * ∑ c ∈ rowSupport false false 0 (.inr 27), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 27), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 27) = ∅ from rfl,
    show rowSupport false false 1 (.inr 27) = {Sum.inr 41} from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.2 1).val 1 1 = ((v.2.2.2 1).val 1 1) + t ^ 2 * (((v.2.2.2 1).val 2 2))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_27_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 27) =
      toCoords F v (.inr 27) + t * ∑ c ∈ rowSupport false true 0 (.inr 27), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 27), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 27) = ∅ from rfl,
    show rowSupport false true 1 (.inr 27) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.2 1).val 1 1 = ((v.2.2.2 1).val 1 1)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_28_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 28) =
      toCoords F v (.inr 28) + t * ∑ c ∈ rowSupport false false 0 (.inr 28), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 28), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 28) = ∅ from rfl,
    show rowSupport false false 1 (.inr 28) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change (action F (modelGenerator F false false t) v).2.1 4 = (v.2.1 4)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_28_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 28) =
      toCoords F v (.inr 28) + t * ∑ c ∈ rowSupport false true 0 (.inr 28), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 28), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 28) = ∅ from rfl,
    show rowSupport false true 1 (.inr 28) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change (action F (modelGenerator F false true t) v).2.1 4 = (v.2.1 4)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_29_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 29) =
      toCoords F v (.inr 29) + t * ∑ c ∈ rowSupport false false 0 (.inr 29), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 29), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 29) = ∅ from rfl,
    show rowSupport false false 1 (.inr 29) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.2 2).val 0 0 = ((v.2.2.2 2).val 0 0)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_29_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 29) =
      toCoords F v (.inr 29) + t * ∑ c ∈ rowSupport false true 0 (.inr 29), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 29), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 29) = ∅ from rfl,
    show rowSupport false true 1 (.inr 29) = {Sum.inr 31} from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.2 2).val 0 0 = ((v.2.2.2 2).val 0 0) + t ^ 2 * (((v.2.2.2 2).val 1 1))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_30_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 30) =
      toCoords F v (.inr 30) + t * ∑ c ∈ rowSupport false false 0 (.inr 30), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 30), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 30) = {Sum.inr 37} from rfl,
    show rowSupport false false 1 (.inr 30) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.2 2).val 0 1 = ((v.2.2.2 2).val 0 1) + t * (((v.2.2.2 2).val 0 2))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_30_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 30) =
      toCoords F v (.inr 30) + t * ∑ c ∈ rowSupport false true 0 (.inr 30), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 30), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 30) = {Sum.inr 31} from rfl,
    show rowSupport false true 1 (.inr 30) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.2 2).val 0 1 = ((v.2.2.2 2).val 0 1) + t * (((v.2.2.2 2).val 1 1))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_31_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 31) =
      toCoords F v (.inr 31) + t * ∑ c ∈ rowSupport false false 0 (.inr 31), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 31), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 31) = ∅ from rfl,
    show rowSupport false false 1 (.inr 31) = {Sum.inr 42} from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.2 2).val 1 1 = ((v.2.2.2 2).val 1 1) + t ^ 2 * (((v.2.2.2 2).val 2 2))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_31_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 31) =
      toCoords F v (.inr 31) + t * ∑ c ∈ rowSupport false true 0 (.inr 31), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 31), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 31) = ∅ from rfl,
    show rowSupport false true 1 (.inr 31) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.2 2).val 1 1 = ((v.2.2.2 2).val 1 1)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_32_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 32) =
      toCoords F v (.inr 32) + t * ∑ c ∈ rowSupport false false 0 (.inr 32), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 32), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 32) = ∅ from rfl,
    show rowSupport false false 1 (.inr 32) = {Sum.inr 43} from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.1 2).val 2 2 = ((v.2.2.1 2).val 2 2) + t ^ 2 * (((v.2.2.1 2).val 1 1))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_32_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 32) =
      toCoords F v (.inr 32) + t * ∑ c ∈ rowSupport false true 0 (.inr 32), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 32), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 32) = ∅ from rfl,
    show rowSupport false true 1 (.inr 32) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.1 2).val 2 2 = ((v.2.2.1 2).val 2 2)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_33_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 33) =
      toCoords F v (.inr 33) + t * ∑ c ∈ rowSupport false false 0 (.inr 33), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 33), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 33) = ∅ from rfl,
    show rowSupport false false 1 (.inr 33) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change (action F (modelGenerator F false false t) v).1 1 2 = (v.1 1 2)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_33_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 33) =
      toCoords F v (.inr 33) + t * ∑ c ∈ rowSupport false true 0 (.inr 33), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 33), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 33) = {Sum.inr 34} from rfl,
    show rowSupport false true 1 (.inr 33) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change (action F (modelGenerator F false true t) v).1 1 2 = (v.1 1 2) + t * ((v.1 0 2))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_34_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 34) =
      toCoords F v (.inr 34) + t * ∑ c ∈ rowSupport false false 0 (.inr 34), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 34), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 34) = ∅ from rfl,
    show rowSupport false false 1 (.inr 34) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change (action F (modelGenerator F false false t) v).1 0 2 = (v.1 0 2)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_34_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 34) =
      toCoords F v (.inr 34) + t * ∑ c ∈ rowSupport false true 0 (.inr 34), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 34), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 34) = ∅ from rfl,
    show rowSupport false true 1 (.inr 34) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change (action F (modelGenerator F false true t) v).1 0 2 = (v.1 0 2)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_35_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 35) =
      toCoords F v (.inr 35) + t * ∑ c ∈ rowSupport false false 0 (.inr 35), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 35), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 35) = ∅ from rfl,
    show rowSupport false false 1 (.inr 35) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.2 1).val 0 2 = ((v.2.2.2 1).val 0 2)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_35_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 35) =
      toCoords F v (.inr 35) + t * ∑ c ∈ rowSupport false true 0 (.inr 35), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 35), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 35) = {Sum.inr 36} from rfl,
    show rowSupport false true 1 (.inr 35) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.2 1).val 0 2 = ((v.2.2.2 1).val 0 2) + t * (((v.2.2.2 1).val 1 2))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_36_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 36) =
      toCoords F v (.inr 36) + t * ∑ c ∈ rowSupport false false 0 (.inr 36), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 36), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 36) = {Sum.inr 41} from rfl,
    show rowSupport false false 1 (.inr 36) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.2 1).val 1 2 = ((v.2.2.2 1).val 1 2) + t * (((v.2.2.2 1).val 2 2))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_36_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 36) =
      toCoords F v (.inr 36) + t * ∑ c ∈ rowSupport false true 0 (.inr 36), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 36), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 36) = ∅ from rfl,
    show rowSupport false true 1 (.inr 36) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.2 1).val 1 2 = ((v.2.2.2 1).val 1 2)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_37_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 37) =
      toCoords F v (.inr 37) + t * ∑ c ∈ rowSupport false false 0 (.inr 37), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 37), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 37) = ∅ from rfl,
    show rowSupport false false 1 (.inr 37) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.2 2).val 0 2 = ((v.2.2.2 2).val 0 2)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_37_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 37) =
      toCoords F v (.inr 37) + t * ∑ c ∈ rowSupport false true 0 (.inr 37), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 37), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 37) = {Sum.inr 38} from rfl,
    show rowSupport false true 1 (.inr 37) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.2 2).val 0 2 = ((v.2.2.2 2).val 0 2) + t * (((v.2.2.2 2).val 1 2))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_38_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 38) =
      toCoords F v (.inr 38) + t * ∑ c ∈ rowSupport false false 0 (.inr 38), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 38), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 38) = {Sum.inr 42} from rfl,
    show rowSupport false false 1 (.inr 38) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.2 2).val 1 2 = ((v.2.2.2 2).val 1 2) + t * (((v.2.2.2 2).val 2 2))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_38_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 38) =
      toCoords F v (.inr 38) + t * ∑ c ∈ rowSupport false true 0 (.inr 38), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 38), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 38) = ∅ from rfl,
    show rowSupport false true 1 (.inr 38) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.2 2).val 1 2 = ((v.2.2.2 2).val 1 2)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_39_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 39) =
      toCoords F v (.inr 39) + t * ∑ c ∈ rowSupport false false 0 (.inr 39), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 39), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 39) = {Sum.inr 43} from rfl,
    show rowSupport false false 1 (.inr 39) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.1 2).val 1 2 = ((v.2.2.1 2).val 1 2) + t * (((v.2.2.1 2).val 1 1))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_39_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 39) =
      toCoords F v (.inr 39) + t * ∑ c ∈ rowSupport false true 0 (.inr 39), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 39), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 39) = {Sum.inr 40} from rfl,
    show rowSupport false true 1 (.inr 39) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.1 2).val 1 2 = ((v.2.2.1 2).val 1 2) + t * (((v.2.2.1 2).val 0 2))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_40_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 40) =
      toCoords F v (.inr 40) + t * ∑ c ∈ rowSupport false false 0 (.inr 40), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 40), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 40) = {Sum.inr 44} from rfl,
    show rowSupport false false 1 (.inr 40) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.1 2).val 0 2 = ((v.2.2.1 2).val 0 2) + t * (((v.2.2.1 2).val 0 1))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_40_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 40) =
      toCoords F v (.inr 40) + t * ∑ c ∈ rowSupport false true 0 (.inr 40), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 40), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 40) = ∅ from rfl,
    show rowSupport false true 1 (.inr 40) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.1 2).val 0 2 = ((v.2.2.1 2).val 0 2)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_41_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 41) =
      toCoords F v (.inr 41) + t * ∑ c ∈ rowSupport false false 0 (.inr 41), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 41), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 41) = ∅ from rfl,
    show rowSupport false false 1 (.inr 41) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.2 1).val 2 2 = ((v.2.2.2 1).val 2 2)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_41_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 41) =
      toCoords F v (.inr 41) + t * ∑ c ∈ rowSupport false true 0 (.inr 41), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 41), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 41) = ∅ from rfl,
    show rowSupport false true 1 (.inr 41) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.2 1).val 2 2 = ((v.2.2.2 1).val 2 2)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_42_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 42) =
      toCoords F v (.inr 42) + t * ∑ c ∈ rowSupport false false 0 (.inr 42), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 42), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 42) = ∅ from rfl,
    show rowSupport false false 1 (.inr 42) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.2 2).val 2 2 = ((v.2.2.2 2).val 2 2)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_42_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 42) =
      toCoords F v (.inr 42) + t * ∑ c ∈ rowSupport false true 0 (.inr 42), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 42), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 42) = ∅ from rfl,
    show rowSupport false true 1 (.inr 42) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.2 2).val 2 2 = ((v.2.2.2 2).val 2 2)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_43_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 43) =
      toCoords F v (.inr 43) + t * ∑ c ∈ rowSupport false false 0 (.inr 43), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 43), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 43) = ∅ from rfl,
    show rowSupport false false 1 (.inr 43) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.1 2).val 1 1 = ((v.2.2.1 2).val 1 1)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_43_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 43) =
      toCoords F v (.inr 43) + t * ∑ c ∈ rowSupport false true 0 (.inr 43), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 43), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 43) = ∅ from rfl,
    show rowSupport false true 1 (.inr 43) = {Sum.inr 45} from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.1 2).val 1 1 = ((v.2.2.1 2).val 1 1) + t ^ 2 * (((v.2.2.1 2).val 0 0))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_44_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 44) =
      toCoords F v (.inr 44) + t * ∑ c ∈ rowSupport false false 0 (.inr 44), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 44), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 44) = ∅ from rfl,
    show rowSupport false false 1 (.inr 44) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.1 2).val 0 1 = ((v.2.2.1 2).val 0 1)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_44_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 44) =
      toCoords F v (.inr 44) + t * ∑ c ∈ rowSupport false true 0 (.inr 44), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 44), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 44) = {Sum.inr 45} from rfl,
    show rowSupport false true 1 (.inr 44) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.1 2).val 0 1 = ((v.2.2.1 2).val 0 1) + t * (((v.2.2.1 2).val 0 0))
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_45_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 45) =
      toCoords F v (.inr 45) + t * ∑ c ∈ rowSupport false false 0 (.inr 45), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 45), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 45) = ∅ from rfl,
    show rowSupport false false 1 (.inr 45) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false false t) v).2.2.1 2).val 0 0 = ((v.2.2.1 2).val 0 0)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_45_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 45) =
      toCoords F v (.inr 45) + t * ∑ c ∈ rowSupport false true 0 (.inr 45), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 45), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 45) = ∅ from rfl,
    show rowSupport false true 1 (.inr 45) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change ((action F (modelGenerator F false true t) v).2.2.1 2).val 0 0 = ((v.2.2.1 2).val 0 0)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_46_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 46) =
      toCoords F v (.inr 46) + t * ∑ c ∈ rowSupport false false 0 (.inr 46), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 46), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 46) = ∅ from rfl,
    show rowSupport false false 1 (.inr 46) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change (action F (modelGenerator F false false t) v).2.1 5 = (v.2.1 5)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_46_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 46) =
      toCoords F v (.inr 46) + t * ∑ c ∈ rowSupport false true 0 (.inr 46), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 46), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 46) = ∅ from rfl,
    show rowSupport false true 1 (.inr 46) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change (action F (modelGenerator F false true t) v).2.1 5 = (v.2.1 5)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_47_false (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false false t) v) (.inr 47) =
      toCoords F v (.inr 47) + t * ∑ c ∈ rowSupport false false 0 (.inr 47), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false false 1 (.inr 47), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false false 0 (.inr 47) = ∅ from rfl,
    show rowSupport false false 1 (.inr 47) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change (action F (modelGenerator F false false t) v).2.1 6 = (v.2.1 6)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem root_47_true (t : F) (v : Space F) :
    toCoords F (action F (modelGenerator F false true t) v) (.inr 47) =
      toCoords F v (.inr 47) + t * ∑ c ∈ rowSupport false true 0 (.inr 47), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false true 1 (.inr 47), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [show rowSupport false true 0 (.inr 47) = ∅ from rfl,
    show rowSupport false true 1 (.inr 47) = ∅ from rfl]
  simp only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,
    Finset.mem_singleton, Sum.inl.injEq, Fin.reduceEq, not_false_eq_true, mul_zero, add_zero]
  change (action F (modelGenerator F false true t) v).2.1 6 = (v.2.1 6)
  have hn01 (d : Fin 3) := (v.2.2.1 d).property 1 0
  have hn02 (d : Fin 3) := (v.2.2.1 d).property 2 0
  have hn12 (d : Fin 3) := (v.2.2.1 d).property 2 1
  have hd01 (d : Fin 3) := (v.2.2.2 d).property 1 0
  have hd02 (d : Fin 3) := (v.2.2.2 d).property 2 0
  have hd12 (d : Fin 3) := (v.2.2.2 d).property 2 1
  simp only [action_mat, action_fixed, action_sym, action_dual,
    row, column, Bool.false_eq_true, reduceIte, Fin.reduceEq, and_self,
    true_and, false_and, and_true, and_false, add_zero, zero_add]
  all_goals
    try simp only [hn01, hn02, hn12, hd01, hd02, hd12]
    ring_nf
    all_goals simp only [htwo, mul_zero, add_zero, zero_add]

private theorem negative_cartan (k : Bool) (t : F) (v : Space F) (r : Fin 4) :
    toCoords F (action F (modelGenerator F false k t) v) (.inl r) =
      toCoords F v (.inl r) + t * ∑ c ∈ rowSupport false k 0 (.inl r), toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false k 1 (.inl r), toCoords F v c := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  cases k <;> fin_cases r <;>
    simp only [toCoords, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, action_mat, action_fixed]
  all_goals simp [rowSupport, row, column, toCoords, finSumFinEquiv]
  all_goals (ring_nf <;> simp [htwo])


public theorem negative_coordinates (k : Bool) (t : F) (v : Space F) (r : Index) :
    toCoords F (action F (modelGenerator F false k t) v) r =
      toCoords F v r + t * ∑ c ∈ rowSupport false k 0 r, toCoords F v c +
        t ^ 2 * ∑ c ∈ rowSupport false k 1 r, toCoords F v c := by
  cases r with
  | inl r => exact negative_cartan F k t v r
  | inr r =>
    cases k

    · fin_cases r
      · exact root_0_false F t v
      · exact root_1_false F t v
      · exact root_2_false F t v
      · exact root_3_false F t v
      · exact root_4_false F t v
      · exact root_5_false F t v
      · exact root_6_false F t v
      · exact root_7_false F t v
      · exact root_8_false F t v
      · exact root_9_false F t v
      · exact root_10_false F t v
      · exact root_11_false F t v
      · exact root_12_false F t v
      · exact root_13_false F t v
      · exact root_14_false F t v
      · exact root_15_false F t v
      · exact root_16_false F t v
      · exact root_17_false F t v
      · exact root_18_false F t v
      · exact root_19_false F t v
      · exact root_20_false F t v
      · exact root_21_false F t v
      · exact root_22_false F t v
      · exact root_23_false F t v
      · exact root_24_false F t v
      · exact root_25_false F t v
      · exact root_26_false F t v
      · exact root_27_false F t v
      · exact root_28_false F t v
      · exact root_29_false F t v
      · exact root_30_false F t v
      · exact root_31_false F t v
      · exact root_32_false F t v
      · exact root_33_false F t v
      · exact root_34_false F t v
      · exact root_35_false F t v
      · exact root_36_false F t v
      · exact root_37_false F t v
      · exact root_38_false F t v
      · exact root_39_false F t v
      · exact root_40_false F t v
      · exact root_41_false F t v
      · exact root_42_false F t v
      · exact root_43_false F t v
      · exact root_44_false F t v
      · exact root_45_false F t v
      · exact root_46_false F t v
      · exact root_47_false F t v
    · fin_cases r
      · exact root_0_true F t v
      · exact root_1_true F t v
      · exact root_2_true F t v
      · exact root_3_true F t v
      · exact root_4_true F t v
      · exact root_5_true F t v
      · exact root_6_true F t v
      · exact root_7_true F t v
      · exact root_8_true F t v
      · exact root_9_true F t v
      · exact root_10_true F t v
      · exact root_11_true F t v
      · exact root_12_true F t v
      · exact root_13_true F t v
      · exact root_14_true F t v
      · exact root_15_true F t v
      · exact root_16_true F t v
      · exact root_17_true F t v
      · exact root_18_true F t v
      · exact root_19_true F t v
      · exact root_20_true F t v
      · exact root_21_true F t v
      · exact root_22_true F t v
      · exact root_23_true F t v
      · exact root_24_true F t v
      · exact root_25_true F t v
      · exact root_26_true F t v
      · exact root_27_true F t v
      · exact root_28_true F t v
      · exact root_29_true F t v
      · exact root_30_true F t v
      · exact root_31_true F t v
      · exact root_32_true F t v
      · exact root_33_true F t v
      · exact root_34_true F t v
      · exact root_35_true F t v
      · exact root_36_true F t v
      · exact root_37_true F t v
      · exact root_38_true F t v
      · exact root_39_true F t v
      · exact root_40_true F t v
      · exact root_41_true F t v
      · exact root_42_true F t v
      · exact root_43_true F t v
      · exact root_44_true F t v
      · exact root_45_true F t v
      · exact root_46_true F t v
      · exact root_47_true F t v
end ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart
