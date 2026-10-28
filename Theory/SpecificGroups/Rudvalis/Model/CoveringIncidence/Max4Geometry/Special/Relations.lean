module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Special.WordComparison
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Special.Certificates
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.RankOneEightCharacteristic.WordFacts

/-!
# Squares and commutators on the literal Rudvalis core words

Transfer the checked small word calculations to Max4Words.generator and
the original marked eight-group. The central masks use the original three
marked words, in order. All statements retain the ambient model embedding.
Source: GLS3 Table 5.3r and pp.291--292; Aschbacher--Smith I.2.2(7), pp.412--413.
-/

namespace Rudvalis.CoveringIncidence.Max4Special
open SylowOvergroups.RadicalCoverage.LocalCover
open CatalogueCertificate Collection Certificate
open scoped commutatorElement
set_option Elab.async false

private theorem eval_append (u v : List (Fin 14)) : eval (u ++ v) = eval u * eval v := by
  simp only [eval, List.map_append, List.prod_append]


public theorem center_word_eq_basis (i : Fin 3) :
    eval (centerWord i) = RankOneEightCharacteristic.basis i := by
  apply modelSubgroup.subtype_injective
  simpa only [eval, ← Coverage.pcWordPermutation_eq, RankOneEightCharacteristic.basis,
    ← elementaryPermutation_eq] using center_word_permutation i

public theorem centralValue_eq (n : Fin 8) : centralValue n =
    (if n.val % 2 = 1 then RankOneEightCharacteristic.basis 0 else 1) *
    (if n.val / 2 % 2 = 1 then RankOneEightCharacteristic.basis 1 else 1) *
    (if n.val / 4 % 2 = 1 then RankOneEightCharacteristic.basis 2 else 1) := by
  unfold centralValue centralWord
  rw [eval_append, eval_append]
  split_ifs <;> simp only [center_word_eq_basis, show eval [] = 1 from rfl]

public theorem centralValue_mem (n : Fin 8) : centralValue n ∈ elementary 2 := by
  rw [centralValue_eq]
  apply Subgroup.mul_mem
  · apply Subgroup.mul_mem
    · split_ifs
      · exact RankOneEightCharacteristic.basis_mem 0
      · exact Subgroup.one_mem _
    · split_ifs
      · exact RankOneEightCharacteristic.basis_mem 1
      · exact Subgroup.one_mem _
  · split_ifs
    · exact RankOneEightCharacteristic.basis_mem 2
    · exact Subgroup.one_mem _


public theorem generator_square (i : Fin 11) :
    Max4Words.generator i * Max4Words.generator i = centralValue (squareCode i) := by
  simp only [generator_eq]
  change eval (word i) * eval (word i) = eval (centralWord (squareCode i))
  rw [← eval_append]
  exact eq_of_collect 460 _ _ (square_check i)

public theorem generator_swap (i j : Fin 11) :
    Max4Words.generator i * Max4Words.generator j =
      centralValue (commutatorCode i j) * (Max4Words.generator j * Max4Words.generator i) := by
  simp only [generator_eq]
  change eval (word i) * eval (word j) =
    eval (centralWord (commutatorCode i j)) * (eval (word j) * eval (word i))
  rw [← eval_append, ← eval_append, ← eval_append]
  exact eq_of_collect 460 _ _ (swap_check i j)

public theorem generator_commutator (i j : Fin 11) :
    ⁅Max4Words.generator i, Max4Words.generator j⁆ = centralValue (commutatorCode i j) := by
  rw [commutatorElement_def, generator_swap]
  group

end Rudvalis.CoveringIncidence.Max4Special
