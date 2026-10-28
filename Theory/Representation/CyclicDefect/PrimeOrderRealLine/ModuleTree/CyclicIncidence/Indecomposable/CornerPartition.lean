module

public import Theory.Character.ModularBlock.PrimitiveCentralIdempotent
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic

/-!
# Central primitivity and partitions of orthogonal idempotents

A nonempty proper partial sum of a complete orthogonal family cannot be
central inside a primitive block. If all corners across a partition vanish
in both directions, multiplication through the complete family makes that
partial sum central. This proves the algebraic partition step underlying
Feit I.13.11 and I.16.7, without any character-theoretic assumptions.
-/

public section
noncomputable section
open scoped BigOperators Classical

namespace ModularBlock

/-- A partition of the nonzero orthogonal summands of a primitive central
idempotent has a nonzero corner across it in at least one direction. -/
theorem exists_cross_corner_of_isCentrallyPrimitive
    {A J : Type*} [Ring A] [Fintype J]
    (b : A) (hb : IsCentrallyPrimitive b) (q : J → A)
    (hq : ∀ i, IsIdempotentElem (q i))
    (hne : ∀ i, q i ≠ 0)
    (horth : Pairwise fun i j => q i * q j = 0)
    (hsum : ∑ i, q i = b)
    (S : Finset J) (hS : S.Nonempty) (hproper : S ≠ Finset.univ) :
    ∃ i j x, i ∈ S ∧ j ∉ S ∧
      (q i * x * q j ≠ 0 ∨ q j * x * q i ≠ 0) := by
  by_contra h
  have hzero (i j : J) (hi : i ∈ S) (hj : j ∉ S) (x : A) :
      q i * x * q j = 0 ∧ q j * x * q i = 0 := by
    constructor
    · by_contra hne'
      exact h ⟨i, j, x, hi, hj, Or.inl hne'⟩
    · by_contra hne'
      exact h ⟨i, j, x, hi, hj, Or.inr hne'⟩
  have hprod (i j : J) : q i * q j = if i = j then q i else 0 := by
    split_ifs with hij
    · subst j
      exact hq i
    · exact horth hij
  let z : A := ∑ i ∈ S, q i
  have hright (j : J) : z * q j = if j ∈ S then q j else 0 := by
    simp [z, Finset.sum_mul, hprod]
  have hleft (j : J) : q j * z = if j ∈ S then q j else 0 := by
    simp [z, Finset.mul_sum, hprod]
  have hqfactor (i : J) : q i * b = q i := by
    rw [← hsum]
    simp [Finset.mul_sum, hprod]
  have hzfactor : z * b = z := by
    simp [z, Finset.sum_mul, hqfactor]
  have hzid : IsIdempotentElem z := by
    change z * z = z
    calc
      z * z = ∑ i ∈ S, z * q i := Finset.mul_sum _ _ _
      _ = z := Finset.sum_congr rfl fun i hi => by rw [hright i, if_pos hi]
  have hzbz (x : A) : z * x * b = z * x * z := by
    calc
      z * x * b = ∑ i ∈ S, ∑ j : J, q i * x * q j := by
        rw [← hsum]
        simp only [z, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_comm
      _ = ∑ i ∈ S, ∑ j ∈ S, q i * x * q j := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (Finset.sum_subset (Finset.subset_univ S)
          (fun j _ hj => (hzero i j hi hj x).1)).symm
      _ = z * x * z := by
        simp only [z, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_comm
  have hbzz (x : A) : b * x * z = z * x * z := by
    calc
      b * x * z = ∑ j ∈ S, ∑ i : J, q i * x * q j := by
        rw [← hsum]
        simp only [z, Finset.sum_mul, Finset.mul_sum]
      _ = ∑ j ∈ S, ∑ i ∈ S, q i * x * q j := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (Finset.sum_subset (Finset.subset_univ S)
          (fun i _ hi => (hzero j i hj hi x).2)).symm
      _ = z * x * z := by
        simp only [z, Finset.sum_mul, Finset.mul_sum]
  have hzcenter : z ∈ Set.center A := by
    apply Semigroup.mem_center_iff.mpr
    intro x
    have hbx : x * b = b * x := Semigroup.mem_center_iff.mp hb.1 x
    have hbz : b * z = z := (Semigroup.mem_center_iff.mp hb.1 z).symm.trans hzfactor
    calc
      x * z = b * x * z := by rw [← hbx, mul_assoc, hbz]
      _ = z * x * z := hbzz x
      _ = z * x * b := (hzbz x).symm
      _ = z * x := by rw [mul_assoc, hbx, ← mul_assoc, hzfactor]
  have hzneq : z ≠ 0 := by
    obtain ⟨i, hi⟩ := hS
    intro hz
    have hi' := hright i
    rw [hz, zero_mul, if_pos hi] at hi'
    exact hne i hi'.symm
  have hzeq : z = b := hb.2.2.2 z hzcenter hzid hzfactor hzneq
  have hall : S = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro j
    by_contra hj
    have hzj := hleft j
    rw [hzeq, hqfactor j, if_neg hj] at hzj
    exact hne j hzj
  exact hproper hall

end ModularBlock
