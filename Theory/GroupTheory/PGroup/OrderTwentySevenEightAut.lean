module

public import Theory.GroupTheory.PGroup.OrderTwentySeven
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Exponent three from an automorphism of order eight

Suppose a group of order 27 has an automorphism of order eight whose fourth
power has exactly three fixed points. Then every element has cube one.

The automorphism excludes a cyclic group of order 27, so ninth powers are
trivial. Cubing is multiplicative, using the class-two calculation in the
noncommutative case. Its image lies in its kernel, so the kernel has order
nine or 27. In the order-nine case, the fourth power of the automorphism
fixes three kernel elements and swaps the other six. This permutation is
odd, contradicting its being a fourth power.

This is an elementary specialization of the exponent conclusion in
M. Suzuki, *A characterization of the 3-dimensional projective unitary group
over a finite field of odd characteristic*, J. Algebra 2 (1965), Lemma 11.
-/

namespace OrderTwentySeven

open scoped IsMulCommutative

/-- An order-eight automorphism with three fixed points for its fourth power
forces a group of order 27 to have exponent three. -/
public theorem cube_eq_one_of_eight_aut {P : Type*} [Group P] [Finite P] (hP : Nat.card P = 27)
    (f : MulAut P) (hf : orderOf f = 8)
    (hfixed : Nat.card {x : P // (f ^ 4) x = x} = 3) :
    ∀ x : P, x ^ 3 = 1 := by
  classical
  have hnotcyc : ¬ IsCyclic P := by
    intro hc
    let : IsCyclic P := hc
    have hd := orderOf_dvd_natCard f
    rw [hf, IsCyclic.card_mulAut, hP] at hd
    norm_num [show Nat.totient 27 = 18 from rfl] at hd
  have hnine (x : P) : x ^ 9 = 1 := by
    have hd : orderOf x ∣ 27 := hP ▸ orderOf_dvd_natCard x
    have hm := Nat.mem_divisors.mpr ⟨hd, (by decide : 27 ≠ 0)⟩
    have he : Nat.divisors 27 = {1, 3, 9, 27} := by decide
    rw [he] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h | h | h
    · exact orderOf_dvd_iff_pow_eq_one.mp (by rw [h]; decide)
    · exact orderOf_dvd_iff_pow_eq_one.mp (by rw [h]; decide)
    · exact orderOf_dvd_iff_pow_eq_one.mp (by rw [h])
    · exact (hnotcyc (isCyclic_iff_exists_orderOf_eq_natCard.mpr
        ⟨x, h.trans hP.symm⟩)).elim
  let cube : P →* P :=
    { toFun := fun x => x ^ 3
      map_one' := one_pow 3
      map_mul' := by
        intro x y
        by_cases hc : IsMulCommutative P
        · let : IsMulCommutative P := hc
          exact mul_pow x y 3
        · exact cube_mul hP hc x y }
  have hrk : cube.range ≤ cube.ker := by
    rintro x ⟨y, rfl⟩
    change (y ^ 3) ^ 3 = 1
    rw [← pow_mul]
    exact hnine y
  have hmul : Nat.card cube.ker * Nat.card cube.range = 27 := by
    have hm := cube.ker.card_mul_index
    rwa [Subgroup.index_ker, hP] at hm
  have hle := Subgroup.card_le_of_le hrk
  have hd : Nat.card cube.ker ∣ 27 := hP ▸ cube.ker.card_subgroup_dvd_card
  have hm := Nat.mem_divisors.mpr ⟨hd, (by decide : 27 ≠ 0)⟩
  have he : Nat.divisors 27 = {1, 3, 9, 27} := by decide
  rw [he] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  have hker : Nat.card cube.ker = 9 ∨ Nat.card cube.ker = 27 := by
    rcases hm with h | h | h | h
    · rw [h] at hmul hle; omega
    · rw [h] at hmul hle; omega
    · exact Or.inl h
    · exact Or.inr h
  suffices hk : Nat.card cube.ker = 27 by
    have htop := Subgroup.eq_top_of_card_eq cube.ker (hk.trans hP.symm)
    intro x
    exact (show x ∈ cube.ker from htop ▸ Subgroup.mem_top x)
  rcases hker with hk | hk
  · let C := (f ^ 4).toMonoidHom.eqLocus (MonoidHom.id P)
    have hC : Nat.card C = 3 := hfixed
    have hCker : C ≤ cube.ker := by
      intro x hx
      exact orderOf_dvd_iff_pow_eq_one.mp (by
        simpa only [hC] using C.orderOf_dvd_natCard hx)
    let r : Equiv.Perm cube.ker :=
      { toFun := fun x => ⟨f x, by
          change (f x) ^ 3 = 1
          rw [← map_pow, show (x : P) ^ 3 = 1 from x.property, map_one]⟩
        invFun := fun x => ⟨f.symm x, by
          change (f.symm x) ^ 3 = 1
          rw [← map_pow, show (x : P) ^ 3 = 1 from x.property, map_one]⟩
        left_inv := fun x => Subtype.ext (f.symm_apply_apply x)
        right_inv := fun x => Subtype.ext (f.apply_symm_apply x) }
    have hr (n : ℕ) (x : cube.ker) : ((r ^ n) x : P) = (f ^ n) x := by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', pow_succ']
        change f ((r ^ n) x : P) = f ((f ^ n) x)
        rw [ih]
    have hr8 : r ^ 8 = 1 := by
      apply Equiv.ext
      intro x
      apply Subtype.ext
      rw [hr, ← hf, pow_orderOf_eq_one]
      rfl
    have hr42 : (r ^ 4) ^ 2 = 1 := by rw [← pow_mul]; exact hr8
    let e : Function.fixedPoints (fun x : cube.ker => (r ^ 4) x) ≃ C :=
      { toFun := fun x => ⟨x.val.val, by
          change (f ^ 4) x.val.val = x.val.val
          rw [← hr]
          exact congrArg Subtype.val x.property⟩
        invFun := fun x => ⟨⟨x.val, hCker x.property⟩, by
          apply Subtype.ext
          rw [hr]
          exact x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hfix : Nat.card (Function.fixedPoints (fun x : cube.ker => (r ^ 4) x)) = 3 :=
      (Nat.card_congr e).trans hC
    let : Fintype cube.ker := Fintype.ofFinite _
    have hs := Equiv.Perm.sign_of_pow_two_eq_one hr42
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hk, hfix] at hs
    have hsign : Equiv.Perm.sign (r ^ 4) = 1 := by
      rw [map_pow]
      rcases Int.units_eq_one_or (Equiv.Perm.sign r) with he | he <;> rw [he] <;> decide
    rw [hsign] at hs
    have hbad := congrArg (fun u : ℤˣ => (u : ℤ)) hs
    norm_num at hbad
  · exact hk

end OrderTwentySeven
