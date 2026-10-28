module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.XCensus.Five
public import Theory.GroupTheory.FixedPointFreeCyclicJoin
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalConfiguration

/-!
# Counting the fibers of a split elementary-sixteen extension of A5

A section identifies the underlying set with the kernel times A5. The
identity fiber has one identity and fifteen involutions. In each of the
fifteen involution fibers, the square-one elements are precisely the four
kernel elements commuting with the section element; the other twelve have
order four. Fixed-point-freeness makes all sixteen elements of each odd
fiber conjugate to its section element. Summing the fibers gives the census.

The action hypotheses here are explicit. `XCensus.Action` proves all of them
for the literal derived F-normalizer, and `XCensus` applies this count there.
Source: Janko (1968), Section 8, Lemma 17, pp.16--17.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups.XCensus
universe u
variable {H : Type u} [Group H] [Finite H]
  (π : H →* alternatingGroup (Fin 5)) (s : alternatingGroup (Fin 5) →* H)
  (hs : ∀ a, π (s a) = a)

include hs in
omit [Finite H] in
private theorem section_order (a : alternatingGroup (Fin 5)) : orderOf (s a) = orderOf a :=
  orderOf_injective s (Function.LeftInverse.injective hs) a

private noncomputable def splitEquiv : H ≃ π.ker × alternatingGroup (Fin 5) where
  toFun x := (⟨x * (s (π x))⁻¹, by simp [MonoidHom.mem_ker, hs]⟩, π x)
  invFun x := x.1 * s x.2
  left_inv x := by simp
  right_inv x := by
    rcases x with ⟨r, a⟩
    have hr : π r = 1 := r.property
    ext <;> simp [map_mul, hs, hr]

include hs in
private theorem count_eq_sum (n : ℕ) :
    Nat.card {x : H // orderOf x = n} =
      ∑ a : alternatingGroup (Fin 5), Nat.card {r : π.ker // orderOf ((r : H) * s a) = n} := by
  classical
  let e := splitEquiv π s hs
  let q : {x : H // orderOf x = n} ≃
      (Σ a : alternatingGroup (Fin 5), {r : π.ker // orderOf ((r : H) * s a) = n}) := {
    toFun x := ⟨(e x).2, ⟨(e x).1, by
      change orderOf (e.symm (e x)) = n
      rw [e.symm_apply_apply]
      exact x.property⟩⟩
    invFun x := ⟨e.symm (x.2, x.1), x.2.property⟩
    left_inv x := Subtype.ext (e.symm_apply_apply x)
    right_inv x := by
      obtain ⟨a, r, hr⟩ := x
      have hrπ : π r = 1 := r.property
      simp [e, splitEquiv, hs, hrπ]
      apply (Subtype.heq_iff_coe_eq (by intro x; simp [hs, hrπ])).mpr
      rfl }
  rw [Nat.card_congr q, Nat.card_sigma]

variable (hpow : ∀ r : π.ker, (r : H) ^ 2 = 1)

include hpow in
omit [Finite H] in
private theorem kernel_order (r : π.ker) : orderOf (r : H) = 1 ∨ orderOf (r : H) = 2 := by
  have hd := orderOf_dvd_of_pow_eq_one (hpow r)
  exact (Nat.dvd_prime Nat.prime_two).mp hd

include hs in
omit [Finite H] in
private theorem coset_not_one (a : alternatingGroup (Fin 5)) (ha : a ≠ 1) (r : π.ker) :
    (r : H) * s a ≠ 1 := by
  intro h
  have hh := congrArg π h
  have hr : π r = 1 := r.property
  simp only [map_mul, hr, one_mul, hs, map_one] at hh
  exact ha hh

include hs hpow in
omit [Finite H] in
private theorem involution_coset_orders (a : alternatingGroup (Fin 5)) (ha : orderOf a = 2)
    (r : π.ker) : orderOf ((r : H) * s a) = 2 ∨ orderOf ((r : H) * s a) = 4 := by
  have hsq : ((r : H) * s a) ^ 2 ∈ π.ker := by
    have hr : π r = 1 := r.property
    simp only [MonoidHom.mem_ker, map_pow, map_mul, hr, one_mul, hs]
    exact ha ▸ pow_orderOf_eq_one a
  have hfour : ((r : H) * s a) ^ 4 = 1 := by
    simpa only [← pow_mul] using hpow ⟨_, hsq⟩
  have hd := orderOf_dvd_of_pow_eq_one hfour
  have hm := Nat.mem_divisors.mpr ⟨hd, (by decide : (4 : ℕ) ≠ 0)⟩
  have he : orderOf ((r : H) * s a) ≠ 1 := by
    intro h
    exact coset_not_one π s hs a (orderOf_eq_prime_iff.mp ha).2 r
      (orderOf_eq_one_iff.mp h)
  rw [show Nat.divisors 4 = {1, 2, 4} by decide] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  exact hm.resolve_left he

include hs hpow in
omit [Finite H] in
private theorem involution_coset_two_iff (a : alternatingGroup (Fin 5)) (ha : orderOf a = 2)
    (r : π.ker) : orderOf ((r : H) * s a) = 2 ↔ Commute (s a) (r : H) := by
  have ht : (s a) ^ 2 = 1 := by rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  have hi : (s a)⁻¹ = s a := inv_eq_iff_mul_eq_one.mpr (by simpa only [pow_two] using ht)
  have hr : (r : H)⁻¹ = r := inv_eq_iff_mul_eq_one.mpr (by simpa only [pow_two] using hpow r)
  rw [orderOf_eq_prime_iff, and_iff_left (coset_not_one π s hs a
    (orderOf_eq_prime_iff.mp ha).2 r), pow_two, ← inv_eq_iff_mul_eq_one,
    mul_inv_rev, hi, hr]
  rfl

variable (hcard : Nat.card π.ker = 16)
  (hfixed : ∀ a : alternatingGroup (Fin 5), orderOf a = 2 →
    Nat.card {r : π.ker // Commute (s a) (r : H)} = 4)
  (hfree : ∀ a : alternatingGroup (Fin 5), orderOf a = 3 ∨ orderOf a = 5 →
    ∀ r ∈ π.ker, Commute (s a) r → r = 1)

include hs hfree in
private theorem odd_coset_order (a : alternatingGroup (Fin 5))
    (ha : orderOf a = 3 ∨ orderOf a = 5) (r : π.ker) :
    orderOf ((r : H) * s a) = orderOf a := by
  rw [orderOf_mul_of_fixedPointFree π.ker (s a) (by rw [normalizer_eq_top]; trivial)
    (hfree a ha) r r.property, section_order π s hs]

include hpow hcard in
private theorem count_one_coset (n : ℕ) :
    Nat.card {r : π.ker // orderOf ((r : H) * s 1) = n} =
      if n = 1 then 1 else if n = 2 then 15 else 0 := by
  classical
  simp only [map_one, mul_one, Subgroup.orderOf_coe]
  by_cases hn1 : n = 1
  · subst n
    simp only [orderOf_eq_one_iff, ↓reduceIte]
    exact Nat.card_unique
  by_cases hn2 : n = 2
  · subst n
    have he (r : π.ker) : orderOf r = 2 ↔ r ≠ 1 := by
      rw [orderOf_eq_prime_iff]
      exact and_iff_right (Subtype.ext (hpow r))
    rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
    let := Fintype.ofFinite π.ker
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard, Nat.card_unique]
    rfl
  have hn : IsEmpty {r : π.ker // orderOf r = n} := ⟨by
    rintro ⟨r, hr⟩
    have ho := kernel_order π hpow r
    rw [Subgroup.orderOf_coe, hr] at ho
    exact ho.elim hn1 hn2⟩
  simp only [Nat.card_of_isEmpty, hn1, hn2, ↓reduceIte]

include hs hpow hcard hfixed in
private theorem count_involution_coset (a : alternatingGroup (Fin 5)) (ha : orderOf a = 2)
    (n : ℕ) : Nat.card {r : π.ker // orderOf ((r : H) * s a) = n} =
      if n = 2 then 4 else if n = 4 then 12 else 0 := by
  classical
  have htwo : Nat.card {r : π.ker // orderOf ((r : H) * s a) = 2} = 4 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight
      (involution_coset_two_iff π s hs hpow a ha))]
    exact hfixed a ha
  by_cases hn2 : n = 2
  · subst n
    exact htwo
  by_cases hn4 : n = 4
  · subst n
    have he (r : π.ker) : orderOf ((r : H) * s a) = 4 ↔
        ¬ orderOf ((r : H) * s a) = 2 := by
      have ho := involution_coset_orders π s hs hpow a ha r
      omega
    rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
    let := Fintype.ofFinite π.ker
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard, htwo]
    rfl
  have hn : IsEmpty {r : π.ker // orderOf ((r : H) * s a) = n} := ⟨by
    rintro ⟨r, hr⟩
    have ho := involution_coset_orders π s hs hpow a ha r
    omega⟩
  simp only [Nat.card_of_isEmpty, hn2, hn4, ↓reduceIte]

include hs hcard hfree in
private theorem count_odd_coset (a : alternatingGroup (Fin 5))
    (ha : orderOf a = 3 ∨ orderOf a = 5) (n : ℕ) :
    Nat.card {r : π.ker // orderOf ((r : H) * s a) = n} =
      if n = orderOf a then 16 else 0 := by
  classical
  simp_rw [odd_coset_order π s hs hfree a ha]
  by_cases hn : n = orderOf a
  · simp only [hn, ↓reduceIte]
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => True.intro))]
    exact hcard
  · have : IsEmpty {r : π.ker // orderOf a = n} := ⟨fun r => hn r.property.symm⟩
    simp only [Nat.card_of_isEmpty, hn, ↓reduceIte]

include hs hpow hcard hfixed hfree in
private theorem fiber_formula (a : alternatingGroup (Fin 5)) (n : ℕ) :
    Nat.card {r : π.ker // orderOf ((r : H) * s a) = n} =
      (if orderOf a = 1 then (if n = 1 then 1 else if n = 2 then 15 else 0) else 0) +
      (if orderOf a = 2 then (if n = 2 then 4 else if n = 4 then 12 else 0) else 0) +
      (if orderOf a = 3 then (if n = 3 then 16 else 0) else 0) +
      (if orderOf a = 5 then (if n = 5 then 16 else 0) else 0) := by
  rcases a5_orders a with ha | ha | ha | ha
  · have ha1 := orderOf_eq_one_iff.mp ha
    subst a
    rw [count_one_coset π s hpow hcard]
    simp
  · rw [count_involution_coset π s hs hpow hcard hfixed a ha]
    simp [ha]
  · rw [count_odd_coset π s hs hcard hfree a (Or.inl ha)]
    simp [ha]
  · rw [count_odd_coset π s hs hcard hfree a (Or.inr ha)]
    simp [ha]

private theorem sum_indicator {A : Type*} [Fintype A] (P : A → Prop) [DecidablePred P] (c : ℕ) :
    (∑ a : A, if P a then c else 0) = Nat.card {a : A // P a} * c := by
  classical
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    Fintype.card_subtype, Nat.card_eq_fintype_card, Nat.cast_id]

include hs hpow hcard hfixed hfree in
/-- Fiber counting for a split elementary-sixteen extension of A5 with the
specified action on its actual kernel. -/
public theorem split_census (n : ℕ) : Nat.card {x : H // orderOf x = n} =
    localOrderCount 75 320 180 384 n := by
  classical
  rw [count_eq_sum π s hs]
  simp_rw [fiber_formula π s hs hpow hcard hfixed hfree, Finset.sum_add_distrib]
  simp only [sum_indicator, a5_count_two, a5_count_three, a5_count_five]
  have h1 : Nat.card {a : alternatingGroup (Fin 5) // orderOf a = 1} = 1 := by
    simp only [orderOf_eq_one_iff]
    exact Nat.card_unique
  rw [h1]
  by_cases hn1 : n = 1
  · subst n; norm_num [localOrderCount]
  by_cases hn2 : n = 2
  · subst n; norm_num [localOrderCount]
  by_cases hn3 : n = 3
  · subst n; norm_num [localOrderCount]
  by_cases hn4 : n = 4
  · subst n; norm_num [localOrderCount]
  by_cases hn5 : n = 5
  · subst n; norm_num [localOrderCount]
  simp [localOrderCount, hn1, hn2, hn3, hn4, hn5]
end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups.XCensus
