module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Tactic

/-!
# The order alternatives and fifth-order classes in A₆

The cycle lengths sum to at most six; parity leaves only the identity,
3, 5, 2+2, 2+4, and 3+3. Thus every element has fourth, third, or fifth
power one. Every element of order five is a five-cycle. Its symmetric-group
centralizer is its cyclic subgroup, and an explicit odd permutation sends
the standard cycle to its square. Splitting symmetric conjugators by parity
therefore gives two distinct internal A₆ classes, represented by any chosen
fifth-order element and its square.

Only the two explicit permutations on six points are checked by reduction;
no enumeration of A₆ or character table is used.

Source application: Z. Janko, *A characterization of the Mathieu simple
groups, I*, J. Algebra 9 (1968), Sections 5–6, pp.9–11.
-/

open Equiv Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.FreeClassA6

private theorem length_bound (l : List ℕ) (hl : ∀ n ∈ l, 2 ≤ n) :
    2 * l.length ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hl
    simp only [List.length_cons, List.sum_cons]
    have := ih hl.2
    omega

private theorem small_even_types (l : List ℕ) (hl : ∀ n ∈ l, 2 ≤ n)
    (hs : l.sum ≤ 6) (he : Even (l.sum + l.length)) :
    l = [] ∨ l = [3] ∨ l = [5] ∨ l = [2,2] ∨ l = [2,4] ∨
      l = [4,2] ∨ l = [3,3] := by
  have hb := length_bound l hl
  have hn : l.length ≤ 3 := by omega
  rcases l with _ | ⟨a, l⟩
  · simp
  rcases l with _ | ⟨b, l⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hl
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero, List.length_cons,
      List.length_nil] at hs he
    rcases he with ⟨t, ht⟩
    have : a = 3 ∨ a = 5 := by omega
    rcases this with rfl | rfl <;> simp
  rcases l with _ | ⟨c, l⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hl
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero, List.length_cons,
      List.length_nil] at hs he
    rcases he with ⟨t, ht⟩
    have : (a = 2 ∧ b = 2) ∨ (a = 2 ∧ b = 4) ∨ (a = 4 ∧ b = 2) ∨
        (a = 3 ∧ b = 3) := by omega
    rcases this with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp
  have : l = [] := by
    apply List.length_eq_zero_iff.mp
    simp only [List.length_cons] at hn
    omega
  subst l
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hl
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero, List.length_cons,
    List.length_nil] at hs he
  rcases he with ⟨t, ht⟩
  omega

/-- The three possible power identities needed for the fixed-vector split. -/
public theorem fourth_or_cube_or_fifth_eq_one (x : alternatingGroup (Fin 6)) : x ^ 4 = 1 ∨ x ^ 3 = 1 ∨ x ^ 5 = 1 := by
  have he : Even (x.val.cycleType.sum + x.val.cycleType.card) := by
    apply (neg_one_pow_eq_one_iff_even (R := ℤˣ) (by norm_num)).mp
    rw [← Perm.sign_of_cycleType]
    exact x.property
  have hs : x.val.cycleType.sum ≤ 6 := x.val.sum_cycleType_le
  have htypes := small_even_types x.val.cycleType.toList
    (by intro n hn; exact Perm.two_le_of_mem_cycleType (by simpa using hn)) (by simpa using hs)
    (by simpa using he)
  have ho : orderOf x = x.val.cycleType.lcm := (orderOf_coe x).symm.trans x.val.lcm_cycleType.symm
  have hd : orderOf x ∣ 4 ∨ orderOf x ∣ 3 ∨ orderOf x ∣ 5 := by
    rw [ho, ← Multiset.coe_toList x.val.cycleType]
    rcases htypes with h | h | h | h | h | h | h <;> rw [h] <;> decide +kernel
  exact hd.imp orderOf_dvd_iff_pow_eq_one.mp (Or.imp orderOf_dvd_iff_pow_eq_one.mp
    orderOf_dvd_iff_pow_eq_one.mp)

private def p : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4, by change Perm.sign _ = 1; decide +kernel⟩

private def b : Perm (Fin 6) := swap 1 2 * swap 2 4 * swap 4 3

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem p_order : orderOf p = 5 := by
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

private theorem b_sign : Perm.sign b = -1 := by decide +kernel

private theorem b_square : b * p.val * b⁻¹ = p.val ^ 2 := by decide +kernel

private theorem p_centralizer : centralizer ({p.val} : Set (Perm (Fin 6))) = zpowers p.val := by
  have hp : orderOf p.val = 5 := (orderOf_coe p).trans p_order
  have hc : p.val.IsCycle := Perm.isCycle_of_prime_order' (hp ▸ (by decide : Nat.Prime 5))
    (by simp [hp])
  have hcard : Nat.card (centralizer ({p.val} : Set (Perm (Fin 6)))) = 5 := by
    rw [Perm.nat_card_centralizer, hc.cycleType, ← hc.orderOf, hp]
    norm_num
  apply (eq_of_le_of_card_ge (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)) ?_).symm
  rw [Nat.card_zpowers, hp, hcard]

private theorem separation : ¬ IsConj p (p ^ 2) := by
  intro h
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have hgp : g.val * p.val * g.val⁻¹ = p.val ^ 2 := congrArg Subtype.val hg
  have hm : b⁻¹ * g.val ∈ centralizer ({p.val} : Set (Perm (Fin 6))) := by
    apply mem_centralizer_singleton_iff.mpr
    calc
      (b⁻¹ * g.val) * p.val = b⁻¹ * (g.val * p.val * g.val⁻¹) * g.val := by group
      _ = b⁻¹ * (b * p.val * b⁻¹) * g.val := by rw [hgp, ← b_square]
      _ = p.val * (b⁻¹ * g.val) := by group
  rw [p_centralizer] at hm
  have he : Perm.sign (b⁻¹ * g.val) = 1 :=
    (zpowers_le.mpr p.property : zpowers p.val ≤ alternatingGroup (Fin 6)) hm
  rw [map_mul, map_inv, b_sign, show Perm.sign g.val = 1 from g.property] at he
  norm_num at he

private theorem standard_covers (x : alternatingGroup (Fin 6)) (hx : orderOf x = 5) :
    IsConj x p ∨ IsConj x (p ^ 2) := by
  have ht (z : alternatingGroup (Fin 6)) (hz : orderOf z = 5) :
      z.val.cycleType = {5} := by
    have hz' : orderOf z.val = 5 := (orderOf_coe z).trans hz
    have hc : z.val.IsCycle := Perm.isCycle_of_prime_order'
      (hz' ▸ (by decide : Nat.Prime 5)) (by simp [hz'])
    rw [hc.cycleType, ← hc.orderOf, hz']
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (Perm.isConj_iff_cycleType_eq.mpr ((ht p p_order).trans (ht x hx).symm))
  rcases Int.units_eq_one_or (Perm.sign g) with he | ho
  · left
    apply IsConj.symm
    exact isConj_iff.mpr ⟨⟨g, he⟩, Subtype.ext hg⟩
  · right
    apply IsConj.symm
    apply isConj_iff.mpr
    refine ⟨⟨g * b⁻¹, ?_⟩, ?_⟩
    · change Perm.sign (g * b⁻¹) = 1
      rw [map_mul, map_inv, ho, b_sign]
      decide
    · apply Subtype.ext
      change (g * b⁻¹) * p.val ^ 2 * (g * b⁻¹)⁻¹ = x.val
      rw [← b_square, ← hg]
      group

/-- A fifth-order element and its square are not conjugate inside A₆. -/
public theorem five_not_isConj_square (x : alternatingGroup (Fin 6)) (hx : orderOf x = 5) :
    ¬ IsConj x (x ^ 2) := by
  intro h
  rcases standard_covers x hx with hc | hc
  · exact separation (hc.symm.trans (h.trans (hc.pow 2)))
  · have hh : IsConj (p ^ 2) ((p ^ 2) ^ 2) := hc.symm.trans (h.trans (hc.pow 2))
    have hh' := hh.pow 3
    simp only [← pow_mul] at hh'
    change IsConj (p ^ 6) (p ^ 12) at hh'
    rw [← pow_mod_orderOf p 6, ← pow_mod_orderOf p 12, p_order] at hh'
    norm_num only [Nat.reduceMod, pow_one] at hh'
    exact separation hh'

/-- Any chosen fifth-order element and its square represent all fifth-order classes. -/
public theorem five_isConj_or_square (x y : alternatingGroup (Fin 6)) (hx : orderOf x = 5)
    (hy : orderOf y = 5) : IsConj x y ∨ IsConj x (y ^ 2) := by
  have hy2 : orderOf (y ^ 2) = 5 := by rw [orderOf_pow' _ (by decide), hy]; decide
  have hn := five_not_isConj_square y hy
  rcases standard_covers y hy with hyc | hyc <;>
    rcases standard_covers (y ^ 2) hy2 with hyc2 | hyc2
  · exact (hn (hyc.trans hyc2.symm)).elim
  · rcases standard_covers x hx with hc | hc
    · exact Or.inl (hc.trans hyc.symm)
    · exact Or.inr (hc.trans hyc2.symm)
  · rcases standard_covers x hx with hc | hc
    · exact Or.inr (hc.trans hyc2.symm)
    · exact Or.inl (hc.trans hyc.symm)
  · exact (hn (hyc.trans hyc2.symm)).elim

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder.FreeClassA6
