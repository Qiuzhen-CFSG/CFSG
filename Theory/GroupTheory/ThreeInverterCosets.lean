module
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.OrderOfElement
public import Theory.GroupTheory.NormalizedSupCard
import Mathlib.Tactic
/-!
# Involutions in a split inverting coset

Suppose `C_G(x) = A⟨z⟩`, with disjoint factors, and an involution `t`
commutes with `z` and inverts the element `x` of order three. Every element
inverting `x` lies uniquely in `At` or `Azt`. Such an element is an
involution exactly when its `A` coordinate is inverted by `t` or `zt`.
The proof constructs the bijection with these two coordinate sets.

This is the coset-counting step in Bender, *Finite groups with large
subgroups* (1974), §4, printed pp.225–226, assertion (4.2).
-/

open scoped Pointwise
namespace Subgroup

private theorem square_mul_iff {G : Type*} [Group G] (a v : G) (hv : v ^ 2 = 1) :
    (a * v) ^ 2 = 1 ↔ v * a * v⁻¹ = a⁻¹ := by
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hv)
  rw [hvi]
  constructor
  · intro he
    apply eq_inv_of_mul_eq_one_right
    simpa only [pow_two, mul_assoc] using he
  · intro he
    calc
      (a * v) ^ 2 = a * (v * a * v) := by simp only [pow_two, mul_assoc]
      _ = 1 := by rw [he, mul_inv_cancel]

variable {G : Type*} [Group G] [Finite G]
/-- The inverting involutions are parametrized by the coordinates inverted
by the two representatives `t` and `zt` of the inverting coset. -/
public theorem inverting_count_eq_two_twisted_counts
    (x z t : G) (hx : orderOf x = 3) (hz : orderOf z = 2)
    (ht : orderOf t = 2) (hzt : Commute z t)
    (htx : t * x * t⁻¹ = x⁻¹) (A : Subgroup G)
    (hn : zpowers z ≤ normalizer (A : Set G)) (hd : Disjoint A (zpowers z))
    (hprod : A ⊔ zpowers z = centralizer ({x} : Set G)) :
    Nat.card {u : G // orderOf u = 2 ∧ u * x * u⁻¹ = x⁻¹} =
      Nat.card {a : A // t * (a : G) * t⁻¹ = (a : G)⁻¹} +
      Nat.card {a : A // (z * t) * (a : G) * (z * t)⁻¹ = (a : G)⁻¹} := by
  classical
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ht2)
  have hzt2 : (z * t) ^ 2 = 1 := by rw [hzt.mul_pow, hz2, ht2, one_mul]
  have hAC : A ≤ centralizer ({x} : Set G) := hprod ▸ le_sup_left
  have hzC : z ∈ centralizer ({x} : Set G) := hprod ▸ mem_sup_right (mem_zpowers z)
  have hzout : z ∉ A := by
    intro he
    have he1 : z = 1 := disjoint_def.mp hd he (mem_zpowers z)
    simp [he1] at hz
  have hxinv : x ≠ x⁻¹ := by
    intro he
    have hx2 : x ^ 2 = 1 := by
      calc
        x ^ 2 = x * x := pow_two x
        _ = x * x⁻¹ := congrArg (x * ·) he
        _ = 1 := mul_inv_cancel x
    have hh := orderOf_dvd_of_pow_eq_one hx2
    rw [hx] at hh
    norm_num at hh
  have hprod_inv (a v : G) (ha : a ∈ centralizer ({x} : Set G))
      (hv : v * x * v⁻¹ = x⁻¹) : (a * v) * x * (a * v)⁻¹ = x⁻¹ := by
    calc
      (a * v) * x * (a * v)⁻¹ = a * (v * x * v⁻¹) * a⁻¹ := by group
      _ = a * x⁻¹ * a⁻¹ := by rw [hv]
      _ = x⁻¹ := by
        have hc : Commute a x := mem_centralizer_singleton_iff.mp ha
        rw [hc.inv_right.eq, mul_inv_cancel_right]
  have hztx := hprod_inv z t hzC htx
  have ho (u : G) (hu : u * x * u⁻¹ = x⁻¹) (hu2 : u ^ 2 = 1) : orderOf u = 2 := by
    apply orderOf_eq_prime hu2
    intro he
    exact hxinv (by simpa only [he, one_mul, inv_one, mul_one] using hu)
  let f : ({a : A // t * (a : G) * t⁻¹ = (a : G)⁻¹} ⊕
      {a : A // (z * t) * (a : G) * (z * t)⁻¹ = (a : G)⁻¹}) →
      {u : G // orderOf u = 2 ∧ u * x * u⁻¹ = x⁻¹} := fun a =>
    match a with
    | .inl a => ⟨(a : G) * t,
        ho _ (hprod_inv _ _ (hAC a.1.property) htx)
          ((square_mul_iff _ _ ht2).mpr a.property),
        hprod_inv _ _ (hAC a.1.property) htx⟩
    | .inr a => ⟨(a : G) * (z * t),
        ho _ (hprod_inv _ _ (hAC a.1.property) hztx)
          ((square_mul_iff _ _ hzt2).mpr a.property),
        hprod_inv _ _ (hAC a.1.property) hztx⟩
  have hcross (a b : A) : (a : G) * t ≠ (b : G) * (z * t) := by
    intro he
    have he' : (a : G) = (b : G) * z := mul_right_cancel (by simpa only [mul_assoc] using he)
    apply hzout
    have hh := A.mul_mem (A.inv_mem b.property) a.property
    simpa only [he', inv_mul_cancel_left] using hh
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have he := congrArg Subtype.val hab
      cases a with
      | inl a =>
        cases b with
        | inl b => exact congrArg Sum.inl (Subtype.ext (Subtype.ext (mul_right_cancel he)))
        | inr b => exact (hcross a b he).elim
      | inr a =>
        cases b with
        | inl b => exact (hcross b a he.symm).elim
        | inr b => exact congrArg Sum.inr (Subtype.ext (Subtype.ext (mul_right_cancel he)))
    · intro u
      have hc : (u : G) * t⁻¹ ∈ centralizer ({x} : Set G) := by
        apply mem_centralizer_singleton_iff.mpr
        apply mul_inv_eq_iff_eq_mul.mp
        calc
          ((u : G) * t⁻¹) * x * ((u : G) * t⁻¹)⁻¹ =
              (u : G) * (t * x * t⁻¹) * (u : G)⁻¹ := by simp only [mul_inv_rev, mul_assoc, hti]
          _ = (u : G) * x⁻¹ * (u : G)⁻¹ := by rw [htx]
          _ = ((u : G) * x * (u : G)⁻¹)⁻¹ := by group
          _ = x := by rw [u.property.2, inv_inv]
      have hc' : (u : G) * t⁻¹ ∈ (A : Set G) * (zpowers z : Set G) := by
        rw [← coe_mul_of_right_le_normalizer_left A (zpowers z) hn, hprod]
        exact hc
      obtain ⟨a, ha, b, hb, hab⟩ := hc'
      change a * b = (u : G) * t⁻¹ at hab
      change b ∈ zpowers z at hb
      have he : a * b * t = u := by rw [hab]; simp
      have hb' : b = 1 ∨ b = z := by
        rw [mem_zpowers_iff_mem_range_orderOf, hz] at hb
        obtain ⟨i, hi, hbi⟩ := Finset.mem_image.mp hb
        have hi2 := Finset.mem_range.mp hi
        interval_cases i
        · exact Or.inl (by simpa using hbi.symm)
        · exact Or.inr (by simpa using hbi.symm)
      have hu2 : (u : G) ^ 2 = 1 := by
        simpa only [u.property.1] using pow_orderOf_eq_one (u : G)
      rcases hb' with hb1 | hbz
      · simp only [hb1, mul_one] at he
        refine ⟨.inl ⟨⟨a, ha⟩, (square_mul_iff a t ht2).mp ?_⟩, Subtype.ext he⟩
        rwa [he]
      · rw [hbz, mul_assoc] at he
        refine ⟨.inr ⟨⟨a, ha⟩, (square_mul_iff a (z * t) hzt2).mp ?_⟩, Subtype.ext he⟩
        rwa [he]
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_sum]

end Subgroup
