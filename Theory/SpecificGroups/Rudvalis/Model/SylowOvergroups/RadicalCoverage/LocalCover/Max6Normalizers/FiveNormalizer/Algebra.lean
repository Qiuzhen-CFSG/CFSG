module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max6Normalizers.FiveNormalizer.Data

/-!
# Closure of the 32 binary words

Toggling one bit in a word multiplies it by the corresponding involution.
This follows by commuting that generator past the preceding factors. The
only finite computation here checks the indices; permutation commutativity
and the unchanged ATLAS words are certified in Data.

Source: the five-generator branch fixed in LocalCover.Data.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate.Five

private theorem toggle_bit : ∀ i j : Fin 5, ∀ n : Fin 32,
    (toggle i n).val.testBit j.val =
      if i = j then !(n.val.testBit j.val) else n.val.testBit j.val := by
  decide +kernel

private theorem factor_toggle (i j : Fin 5) (n : Fin 32) :
    factor j (toggle i n) = if i = j then gen j * factor j n else factor j n := by
  simp only [factor, toggle_bit]
  by_cases h : i = j
  · subst j
    cases hb : n.val.testBit i.val <;> simp [gen_sq]
  · simp only [h, ite_false]

private theorem gen_comm_factor (i j : Fin 5) (n : Fin 32) :
    Commute (gen i) (factor j n) := by
  unfold factor
  split
  · exact gen_comm i j
  · exact Commute.one_right _

public theorem gen_mul_word (i : Fin 5) (n : Fin 32) :
    gen i * word n = word (toggle i n) := by
  fin_cases i
  all_goals norm_num [word, factor_toggle, Fin.ext_iff, Fin.coe_ofNat_eq_mod, mul_assoc]
  · rw [(gen_comm_factor 1 0 n).left_comm]
  · change gen 2 * (factor 0 n * (factor 1 n * (factor 2 n * (factor 3 n * factor 4 n)))) =
      factor 0 n * (factor 1 n * ((gen 2 * factor 2 n) * (factor 3 n * (factor 4 n))))
    simp only [mul_assoc]
    rw [(gen_comm_factor 2 0 n).left_comm, (gen_comm_factor 2 1 n).left_comm]
  · change gen 3 * (factor 0 n * (factor 1 n * (factor 2 n * (factor 3 n * factor 4 n)))) =
      factor 0 n * (factor 1 n * (factor 2 n * ((gen 3 * factor 3 n) * (factor 4 n))))
    simp only [mul_assoc]
    rw [(gen_comm_factor 3 0 n).left_comm, (gen_comm_factor 3 1 n).left_comm,
      (gen_comm_factor 3 2 n).left_comm]
  · change gen 4 * (factor 0 n * (factor 1 n * (factor 2 n * (factor 3 n * factor 4 n)))) =
      factor 0 n * (factor 1 n * (factor 2 n * (factor 3 n * ((gen 4 * factor 4 n)))))
    rw [(gen_comm_factor 4 0 n).left_comm, (gen_comm_factor 4 1 n).left_comm,
      (gen_comm_factor 4 2 n).left_comm, (gen_comm_factor 4 3 n).left_comm]

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate.Five
