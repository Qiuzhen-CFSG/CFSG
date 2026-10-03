module

public import Theory.GroupTheory.NormalFourCentralizer
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Cyclic-four sections and centralization of a normal four

Every element of square one in a cyclic group of order four is a square.
Consequently, if a subgroup has a cyclic quotient of order four with kernel
centralizing a normal four, each of its involutions centralizes that four:
lift a square root in the quotient and use that squares act trivially on a
normal four in a two-group.

This is the short step from the five-normalizer section `K` to centralization
of `W` in Janko–Thompson, Math. Z. 113 (1970), §4, printed p.390.
Constructing that section is a separate action-theoretic input.
-/

namespace Subgroup

/-- Squares and a kernel contain every involution when the quotient is cyclic
of order four. No commutativity assumption on the original group is needed. -/
public theorem mem_of_square_eq_one_of_cyclic_four_quotient
    {P : Type*} [Group P] [Finite P]
    (Z C : Subgroup P) [Z.Normal] [IsCyclic (P ⧸ Z)]
    (hcard : Nat.card (P ⧸ Z) = 4) (hZC : Z ≤ C)
    (hsq : ∀ a : P, a ^ 2 ∈ C) (t : P) (ht : t ^ 2 = 1) : t ∈ C := by
  let q := QuotientGroup.mk' Z
  have hqt : (q t) ^ 2 = 1 := by rw [← map_pow, ht, map_one]
  have hroot : ∃ b : P ⧸ Z, b ^ 2 = q t := by
    by_cases ht1 : q t = 1
    · exact ⟨1, by simp [ht1]⟩
    obtain ⟨b, hb⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P ⧸ Z)
    rw [hcard] at hb
    have hb2 : orderOf (b ^ 2) = 2 := by rw [orderOf_pow, hb]; norm_num
    exact ⟨b, IsCyclic.eq_of_orderOf_eq_two hb2 (orderOf_eq_prime hqt ht1)⟩
  obtain ⟨b, hb⟩ := hroot
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective Z b
  have haZ : (a ^ 2)⁻¹ * t ∈ Z := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q ((a ^ 2)⁻¹ * t) = 1
    rw [map_mul, map_inv, map_pow, hb, inv_mul_cancel]
  have hmem := C.mul_mem (hsq a) (hZC haZ)
  simpa only [mul_inv_cancel_left] using hmem

/-- An involution in a cyclic-four section whose kernel centralizes a normal
four centralizes that four. -/
public theorem involution_centralizes_normal_four_of_cyclic_four_section
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (E : Subgroup P) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (A : Subgroup P) (Z : Subgroup A) [Z.Normal] [IsCyclic (A ⧸ Z)]
    (hcard : Nat.card (A ⧸ Z) = 4)
    (hZC : Z ≤ (centralizer (E : Set P)).comap A.subtype)
    (t : A) (ht : t ^ 2 = 1) : (t : P) ∈ centralizer (E : Set P) := by
  apply mem_of_square_eq_one_of_cyclic_four_quotient Z
    ((centralizer (E : Set P)).comap A.subtype) hcard hZC ?_ t ht
  intro a
  have hb := centralizer_index_le_two_of_normal_four hP E hE
  have hn := (centralizer (E : Set P)).index_ne_zero_of_finite
  have hi : (centralizer (E : Set P)).index = 1 ∨
      (centralizer (E : Set P)).index = 2 := by omega
  change (a : P) ^ 2 ∈ centralizer (E : Set P)
  rcases hi with hi | hi
  · rw [index_eq_one.mp hi]
    trivial
  · exact sq_mem_of_index_two hi a

end Subgroup
