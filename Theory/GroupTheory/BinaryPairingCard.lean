module
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Tactic

/-!
# Kernel orders in finite binary pairings

Double-counting the pairs on which a pairing is trivial gives
`|A| |ker(f.flip)| = |B| |ker(f)|` for a pairing into a group of order two.
Every nontrivial character has a kernel of index two. No nondegeneracy or
commutativity assumption on the source groups is needed.
This is the counting form of finite binary duality, used for the central
commutator pairing in Parrott (1972), pp.673–674.
-/

namespace MonoidHom
open scoped BigOperators

private theorem binary_character_kernel_card
    {A C : Type*} [Group A] [Finite A] [CommGroup C] [Finite C]
    (hC : Nat.card C = 2) (f : A →* C) [Decidable (f = 1)] :
    2 * Nat.card f.ker = Nat.card A + if f = 1 then Nat.card A else 0 := by
  classical
  by_cases hf : f = 1
  · subst f
    simp
    omega
  · have hr : Nat.card f.range = 2 := by
      have hd := f.range.card_subgroup_dvd_card
      rw [hC] at hd
      rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with h | h
      · have hb := Subgroup.card_eq_one.mp h
        apply hf.elim
        ext a
        have ha : f a ∈ f.range := ⟨a, rfl⟩
        simpa only [hb, Subgroup.mem_bot, MonoidHom.one_apply] using ha
      · exact h
    have hc := f.ker.index_mul_card
    rw [Subgroup.index_ker, hr] at hc
    simpa only [if_neg hf, add_zero] using hc

/-- The two kernels of a finite pairing into a group of order two have
complementary relative orders. -/
public theorem binary_pairing_kernel_card
    {A B C : Type*} [Group A] [Finite A] [Group B] [Finite B]
    [CommGroup C] [Finite C] (hC : Nat.card C = 2)
    (f : A →* (B →* C)) :
    Nat.card A * Nat.card f.flip.ker = Nat.card B * Nat.card f.ker := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let : Fintype B := Fintype.ofFinite B
  have row (a : A) :
      2 * (∑ b : B, if f a b = 1 then 1 else 0) =
        Nat.card B + if f a = 1 then Nat.card B else 0 := by
    have hc := binary_character_kernel_card hC (f a)
    have hk : Nat.card (f a).ker = ∑ b : B, if f a b = 1 then 1 else 0 := by
      rw [Nat.card_eq_fintype_card]
      simp only [Fintype.card_subtype, Finset.card_filter, MonoidHom.mem_ker]
    rw [hk] at hc
    exact hc
  have col (b : B) :
      2 * (∑ a : A, if f a b = 1 then 1 else 0) =
        Nat.card A + if f.flip b = 1 then Nat.card A else 0 := by
    have hc := binary_character_kernel_card hC (f.flip b)
    have hk : Nat.card (f.flip b).ker = ∑ a : A, if f a b = 1 then 1 else 0 := by
      rw [Nat.card_eq_fintype_card]
      simp only [Fintype.card_subtype, Finset.card_filter, MonoidHom.mem_ker, flip_apply]
    rw [hk] at hc
    exact hc
  have hk : (∑ a : A, if f a = 1 then Nat.card B else 0) =
      Nat.card f.ker * Nat.card B := by
    rw [Nat.card_eq_fintype_card (α := f.ker), Fintype.card_subtype, Finset.card_filter]
    simp only [MonoidHom.mem_ker]
    simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  have hl : (∑ b : B, if f.flip b = 1 then Nat.card A else 0) =
      Nat.card f.flip.ker * Nat.card A := by
    rw [Nat.card_eq_fintype_card (α := f.flip.ker), Fintype.card_subtype, Finset.card_filter]
    simp only [MonoidHom.mem_ker]
    simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  have hh : (∑ a : A, (Nat.card B + if f a = 1 then Nat.card B else 0)) =
      ∑ b : B, (Nat.card A + if f.flip b = 1 then Nat.card A else 0) := by
    simp_rw [← row, ← col, Finset.mul_sum]
    exact Finset.sum_comm
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    hk, hl, ← Nat.card_eq_fintype_card] at hh
  nlinarith

end MonoidHom
