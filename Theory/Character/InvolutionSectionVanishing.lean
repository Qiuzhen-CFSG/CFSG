module

public import Theory.Character.ClassSumFormula

/-!
# Involution class products vanish on a two-section

Suppose no conjugate of `J` inverts the two-element `u`. Then no product of
two conjugates of `J` has the form `u * v`, with `v` of odd order commuting
with `u`. Indeed, `u` is a power of `u * v`, and either involution inverts
their product and all its powers. The class-product formula consequently
gives a vanishing sum over the complete family of ordinary characters.

Source: Brauer, *Some applications of the theory of blocks of characters
of finite groups II* (1964),
Section IV, Proposition 4 and Corollary 1, pp. 312–313. This is the ordinary
character relation (4.3); restricting it to a block requires subsection
separation, a separate modular character theorem.
-/

public section
noncomputable section

namespace Theory.Character

open scoped BigOperators
attribute [local instance] Fintype.ofFinite

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem exists_pow_mul_eq_twoElement {u v : G}
    (hu : ∃ n : ℕ, u ^ (2 ^ n) = 1) (hv : Odd (orderOf v))
    (hc : Commute u v) : ∃ m : ℕ, (u * v) ^ m = u := by
  obtain ⟨n, hn⟩ := hu
  have hcop : (orderOf v).Coprime (orderOf u) :=
    (hv.coprime_two_right.pow_right n).of_dvd_right (orderOf_dvd_of_pow_eq_one hn)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨orderOf v * m, ?_⟩
  rw [pow_mul, hc.mul_pow, pow_orderOf_eq_one, mul_one]
  exact hm

omit [Finite G] in
/-- The square of an involution class has no coefficient on a two-section
whose two-element is inverted by none of its members. -/
theorem classSumPairCount_eq_zero_on_twoSection (u J : G)
    (hu : ∃ n : ℕ, u ^ (2 ^ n) = 1) (hJ : J * J = 1)
    (hno : ∀ t : G, IsConj J t → t * u * t⁻¹ ≠ u⁻¹)
    (v : G) (hv : Odd (orderOf v)) (hc : Commute u v) :
    classSumPairCountMul (ConjClasses.mk J) (ConjClasses.mk J) (u * v) = 0 := by
  classical
  rw [classSumPairCountMul_eq_card]
  apply Nat.card_eq_zero.mpr
  apply Or.inl
  refine ⟨fun p => ?_⟩
  rcases p with ⟨⟨x, y⟩, hxy⟩
  have hconj (a : (ConjClasses.mk J).carrier) : IsConj J (a : G) :=
    ConjClasses.mk_eq_mk_iff_isConj.mp
      (ConjClasses.mem_carrier_iff_mk_eq.mp a.property).symm
  have hsquare (a : (ConjClasses.mk J).carrier) : (a : G) * a = 1 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp (hconj a)
    rw [← hg]
    calc
      _ = g * (J * J) * g⁻¹ := by group
      _ = 1 := by rw [hJ]; simp
  have hxinv : (x : G)⁻¹ = x := inv_eq_of_mul_eq_one_left (hsquare x)
  have hyinv : (y : G)⁻¹ = y := inv_eq_of_mul_eq_one_left (hsquare y)
  have hinv : (MulAut.conj (x : G)) (u * v) = (u * v)⁻¹ := by
    rw [MulAut.conj_apply, ← hxy, mul_inv_rev, hxinv, hyinv]
    simp only [← mul_assoc, hsquare x, one_mul]
  obtain ⟨m, hm⟩ := exists_pow_mul_eq_twoElement hu hv hc
  apply hno x (hconj x)
  change (MulAut.conj (x : G)) u = u⁻¹
  rw [← hm, map_pow, hinv, inv_pow]

/-- The all-character involution-weighted relation holds throughout the
two-section. Its restriction to a block is a further modular step. -/
theorem involution_weighted_sum_eq_zero_on_twoSection
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (χ : ι → ConjClassFunction G) (hχ : IsCompleteIrreducibleCharacterFamily χ)
    (u J : G) (hu : ∃ n : ℕ, u ^ (2 ^ n) = 1) (hJ : J * J = 1)
    (hno : ∀ t : G, IsConj J t → t * u * t⁻¹ ≠ u⁻¹)
    (v : G) (hv : Odd (orderOf v)) (hc : Commute u v) :
    ∑ i, χ i (ConjClasses.mk (u * v)) * χ i (ConjClasses.mk J) ^ 2 /
      χ i (ConjClasses.mk 1) = 0 := by
  classical
  have h := classSum_expansion_mul_of_involutions (ConjClasses.mk J) (ConjClasses.mk J)
    J J ConjClasses.mem_carrier_mk ConjClasses.mem_carrier_mk hJ hJ χ hχ (u * v)
  rw [classSumPairCount_eq_zero_on_twoSection u J hu hJ hno v hv hc] at h
  let : Nonempty (ConjClasses.mk J).carrier := ⟨⟨J, ConjClasses.mem_carrier_mk⟩⟩
  have hclass : (Nat.card (ConjClasses.mk J).carrier : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := (ConjClasses.mk J).carrier)).ne'
  have hgroup : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  rw [Nat.cast_zero] at h
  have hsum := (mul_eq_zero.mp h.symm).resolve_left
    (div_ne_zero (mul_ne_zero hclass hclass) hgroup)
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro i _
  ring

end Theory.Character
