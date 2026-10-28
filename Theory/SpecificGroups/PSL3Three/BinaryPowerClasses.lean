module

public import Theory.SpecificGroups.PSL3Three.Subgroups
public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Binary-power conjugacy coverage in PSL₃(3)

An upper bound of seven odd-order conjugacy classes makes seven explicit native
classes exhaustive. Identity and the two unipotent Jordan types account for
three. The Singer matrix and its second, fourth and eighth powers have distinct
pairs of matrix trace and inverse trace, giving the other four. A quadratic
matrix identity distinguishes the two unipotents.

Consequently every odd-order element is conjugate to an iterated square of one
of four representatives. All matrix comparisons are kernel-checked; the class
upper bound remains an independent input. This is the group calculation used by
the native characteristic-two degree-sixteen Frobenius obstruction.

Source context: the characteristic-two PSL₃(3) calculation used in
Guralnick--Malle, *Classification of 2F-modules I*, Proposition 4.2.
-/

open Matrix
namespace Matrix.PSL3Three.BinaryPowerClasses

private def r : Fin 7 → SL :=
  ![1, ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩,
    ⟨!![1, 1, 0; 0, 1, 1; 0, 0, 1], by decide⟩,
    singerGenerator, singerGenerator ^ 2, singerGenerator ^ 4, singerGenerator ^ 8]

private theorem trace_isConj {a b : SL} (h : IsConj a b) :
    a.val.trace = b.val.trace := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  change a.val.trace = (c.val * a.val * (c⁻¹).val).trace
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one, one_mul]

private theorem inv_isConj {a b : SL} (h : IsConj a b) : IsConj a⁻¹ b⁻¹ := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  apply isConj_iff.mpr
  exact ⟨c, by simp [mul_assoc]⟩

private theorem quad_isConj {a b : SL} (h : IsConj a b)
    (ha : a.val * a.val + a.val + 1 = 0) : b.val * b.val + b.val + 1 = 0 := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  have hl : (c⁻¹).val * c.val = 1 := by
    rw [← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one]
  have hr : c.val * (c⁻¹).val = 1 := by
    rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]
  change (c.val * a.val * (c⁻¹).val) * (c.val * a.val * (c⁻¹).val) +
    c.val * a.val * (c⁻¹).val + 1 = 0
  calc
    _ = c.val * (a.val * a.val + a.val + 1) * (c⁻¹).val := by
      simp only [mul_add, add_mul, mul_one]
      simp only [mul_assoc, ← mul_assoc (c⁻¹).val c.val, hl, one_mul, hr]
    _ = 0 := by rw [ha, mul_zero, zero_mul]

private theorem pair_trace (i j : Fin 7)
    (h : ((r i).val.trace, ((r i)⁻¹).val.trace) =
      ((r j).val.trace, ((r j)⁻¹).val.trace)) :
    i = j ∨ (i < 3 ∧ j < 3) := by
  revert i j
  decide

private theorem not_conj_unipotents : ¬ IsConj (r 1) (r 2) := by
  intro h
  have hq := quad_isConj h (by decide)
  exact (by decide : (r 2).val * (r 2).val + (r 2).val + 1 ≠ 0) hq

private theorem pairwise_not_conj : Pairwise fun i j => ¬ IsConj (r i) (r j) := by
  intro i j hij hc
  have ht := pair_trace i j (Prod.ext (trace_isConj hc) (trace_isConj (inv_isConj hc)))
  rcases ht with he | ⟨hi, hj⟩
  · exact hij he
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  have hne1 : r 1 ≠ 1 := by decide
  have hne2 : r 2 ≠ 1 := by decide
  rcases hi' with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl
  · exact hij rfl
  · exact hne1 (isConj_one_right.mp hc)
  · exact hne2 (isConj_one_right.mp hc)
  · exact hne1 (isConj_one_left.mp hc)
  · exact hij rfl
  · exact not_conj_unipotents hc
  · exact hne2 (isConj_one_left.mp hc)
  · exact not_conj_unipotents hc.symm
  · exact hij rfl

private theorem odd_r (i : Fin 7) : ¬ 2 ∣ orderOf (r i) := by
  have hp : (r i) ^ 3 = 1 ∨ (r i) ^ 13 = 1 := by
    fin_cases i
    · left; decide
    · left; decide
    · left; decide
    · right; exact singerGenerator_pow_thirteen
    · right
      change (singerGenerator ^ 2) ^ 13 = 1
      rw [← pow_mul, Nat.mul_comm 2 13, pow_mul, singerGenerator_pow_thirteen, one_pow]
    · right
      change (singerGenerator ^ 4) ^ 13 = 1
      rw [← pow_mul, Nat.mul_comm 4 13, pow_mul, singerGenerator_pow_thirteen, one_pow]
    · right
      change (singerGenerator ^ 8) ^ 13 = 1
      rw [← pow_mul, Nat.mul_comm 8 13, pow_mul, singerGenerator_pow_thirteen, one_pow]
  intro hd
  rcases hp with hp | hp
  · have : 2 ∣ 3 := hd.trans (orderOf_dvd_of_pow_eq_one hp)
    norm_num at this
  · have : 2 ∣ 13 := hd.trans (orderOf_dvd_of_pow_eq_one hp)
    norm_num at this

/-- At most seven odd classes plus seven explicit native witnesses exhausts them. -/
public theorem cover_of_class_bound
    (hclasses : Nat.card (ConjClasses.mk ''
      {g : PSL | ¬ 2 ∣ orderOf g}) ≤ 7) :
    ∃ s : Fin 4 → PSL, ∀ g : PSL, ¬ 2 ∣ orderOf g →
      ∃ i n, IsConj g (s i ^ (2 ^ n)) := by
  classical
  let C := ConjClasses.mk '' {g : PSL | ¬ 2 ∣ orderOf g}
  let f : Fin 7 → C := fun i => ⟨ConjClasses.mk (project (r i)), by
    refine ⟨project (r i), ?_, rfl⟩
    change ¬ 2 ∣ orderOf (project (r i))
    simpa only [orderOf_injective project project_injective] using odd_r i⟩
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    apply pairwise_not_conj hne
    have hc := ConjClasses.mk_eq_mk_iff_isConj.mp (congrArg Subtype.val hij)
    have he := equiv.symm.toMonoidHom.map_isConj hc
    simpa only [MulEquiv.coe_toMonoidHom, ← equiv_apply, MulEquiv.symm_apply_apply] using he
  have hsur := (hinj.bijective_of_nat_card_le (by simpa using hclasses)).surjective
  refine ⟨![project (r 0), project (r 1), project (r 2), project (r 3)], ?_⟩
  intro g hg
  obtain ⟨j, hj⟩ := hsur ⟨ConjClasses.mk g, ⟨g, hg, rfl⟩⟩
  have hc : IsConj g (project (r j)) :=
    (ConjClasses.mk_eq_mk_iff_isConj.mp (congrArg Subtype.val hj)).symm
  fin_cases j
  · exact ⟨0, 0, by simpa using hc⟩
  · exact ⟨1, 0, by simpa using hc⟩
  · exact ⟨2, 0, by simpa using hc⟩
  · exact ⟨3, 0, by simpa using hc⟩
  · exact ⟨3, 1, by simpa [r, map_pow] using hc⟩
  · exact ⟨3, 2, by simpa [r, map_pow] using hc⟩
  · exact ⟨3, 3, by simpa [r, map_pow] using hc⟩

end Matrix.PSL3Three.BinaryPowerClasses
