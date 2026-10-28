module

public import Theory.SpecificGroups.AlternatingSix.GoldenClassGeometry.Representatives

/-!
# Conjugacy classes and centralizers in A₆

Seven pairwise nonconjugate representatives have class sizes
1, 45, 40, 40, 90, 72 and 72. Their disjoint union therefore has order 360,
so it exhausts the actual alternating group on six letters. Conjugation
transports the representative centralizer calculations to every element.
For order five, inversion preserves each class and squaring exchanges them.

The finite certificates are confined to `Representatives`; completeness
uses the orbit-stabilizer formula and finite cardinality, without another
enumeration of conjugacy classes.

Source: standard alternating-group conjugacy calculations; Janko,
*A characterization of the Mathieu simple groups, I* (1968), §6, pp.10–11.
-/

public section

namespace AlternatingSix.GoldenClassGeometry
open Equiv
open scoped BigOperators

private theorem conj_order {G : Type*} [Group G] {x y : G} (h : IsConj x y) :
    orderOf x = orderOf y := by
  obtain ⟨c, hc⟩ := h
  exact hc.orderOf_eq _

private theorem conj_centralizer_card {G : Type*} [Group G] {x y : G}
    (h : IsConj x y) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) =
      Nat.card (Subgroup.centralizer ({y} : Set G)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  let e := MulAut.conj c
  apply Nat.card_congr (Equiv.subtypeEquiv e.toEquiv ?_)
  intro z
  simp only [Subgroup.mem_centralizer_singleton_iff]
  change z * x = x * z ↔ e z * e x = e x * e z
  rw [← e.map_mul, ← e.map_mul, e.injective.eq_iff]

private theorem conj_inv' {G : Type*} [Group G] {x y : G} (h : IsConj x y) :
    IsConj x⁻¹ y⁻¹ := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  exact isConj_iff.mpr ⟨c, (conj_inv).symm⟩

private theorem class_card {G : Type*} [Group G] [Fintype G] (g : G) :
    Nat.card (ConjClasses.mk g).carrier =
      Nat.card G / Nat.card (Subgroup.centralizer ({g} : Set G)) := by
  classical
  rw [Nat.card_eq_fintype_card, ConjClasses.card_carrier,
    Subgroup.centralizer_eq_comap_stabilizer]
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  rfl

private theorem covers_of_class_sizes {G : Type*} [Group G] [Fintype G]
    {n : ℕ} (r : Fin n → G)
    (hi : Function.Injective (fun i => ConjClasses.mk (r i)))
    (hs : ∑ i, Nat.card (ConjClasses.mk (r i)).carrier = Nat.card G) :
    ∀ x : G, ∃ i, IsConj (r i) x := by
  let f : (Σ i, (ConjClasses.mk (r i)).carrier) → G := fun a => a.2.1
  have hf : Function.Injective f := by
    rintro ⟨i, x, hx⟩ ⟨j, y, hy⟩ h
    change x = y at h
    subst y
    have hij : i = j := hi ((ConjClasses.mem_carrier_iff_mk_eq.mp hx).symm.trans
      (ConjClasses.mem_carrier_iff_mk_eq.mp hy))
    subst j
    rfl
  have hc : Nat.card (Σ i, (ConjClasses.mk (r i)).carrier) = Nat.card G := by
    rw [Nat.card_sigma]
    exact hs
  have hsur := (Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hc⟩ |>.2
  intro x
  obtain ⟨⟨i, y, hy⟩, h⟩ := hsur x
  exact ⟨i, h ▸ hy⟩

/-- The seven representatives define distinct A₆ conjugacy classes. -/
theorem representatives_injective : Function.Injective (fun i => ConjClasses.mk (rep i)) := by
  intro i j h
  have hc := ConjClasses.mk_eq_mk_iff_isConj.mp h
  have ho := conj_order hc
  rw [rep_orders, rep_orders] at ho
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals norm_num [orders] at ho
  · exact (three_not_conj hc).elim
  · exact (three_not_conj hc.symm).elim
  · exact (five_nonsquare hc).elim
  · exact (five_nonsquare hc.symm).elim

/-- Every even permutation is conjugate in A₆ to one of the seven representatives. -/
theorem representatives_cover (x : A6) : ∃ i, IsConj (rep i) x := by
  apply covers_of_class_sizes rep representatives_injective
  simp_rw [class_card, rep_cents]
  rw [nat_card_alternatingGroup]
  norm_num [Fin.sum_univ_succ, cents, Nat.factorial]

/-- The actual alternating group on six letters has seven conjugacy classes. -/
theorem class_count : Nat.card (ConjClasses A6) = 7 := by
  have hs : Function.Surjective (fun i => ConjClasses.mk (rep i)) := by
    intro c
    obtain ⟨x, rfl⟩ := ConjClasses.mk_surjective c
    obtain ⟨i, hi⟩ := representatives_cover x
    exact ⟨i, ConjClasses.mk_eq_mk_iff_isConj.mpr hi⟩
  have hc := Nat.card_eq_of_bijective _ ⟨representatives_injective, hs⟩
  simpa using hc.symm

theorem centralizer_two (x : A6) (hx : orderOf x = 2) :
    Nat.card (Subgroup.centralizer ({x} : Set A6)) = 8 := by
  obtain ⟨i, hi⟩ := representatives_cover x
  rw [← conj_centralizer_card hi, rep_cents]
  have ho : orders i = 2 := (rep_orders i).symm.trans ((conj_order hi).trans hx)
  fin_cases i <;> simp_all [orders, cents]

theorem centralizer_three (x : A6) (hx : orderOf x = 3) :
    Nat.card (Subgroup.centralizer ({x} : Set A6)) = 9 := by
  obtain ⟨i, hi⟩ := representatives_cover x
  rw [← conj_centralizer_card hi, rep_cents]
  have ho : orders i = 3 := (rep_orders i).symm.trans ((conj_order hi).trans hx)
  fin_cases i <;> simp_all [orders, cents]

theorem centralizer_four (x : A6) (hx : orderOf x = 4) :
    Nat.card (Subgroup.centralizer ({x} : Set A6)) = 4 := by
  obtain ⟨i, hi⟩ := representatives_cover x
  rw [← conj_centralizer_card hi, rep_cents]
  have ho : orders i = 4 := (rep_orders i).symm.trans ((conj_order hi).trans hx)
  fin_cases i <;> simp_all [orders, cents]

theorem centralizer_five (x : A6) (hx : orderOf x = 5) :
    Nat.card (Subgroup.centralizer ({x} : Set A6)) = 5 := by
  obtain ⟨i, hi⟩ := representatives_cover x
  rw [← conj_centralizer_card hi, rep_cents]
  have ho : orders i = 5 := (rep_orders i).symm.trans ((conj_order hi).trans hx)
  fin_cases i <;> simp_all [orders, cents]

theorem order_five_inverse (x : A6) (hx : orderOf x = 5) : IsConj x x⁻¹ := by
  obtain ⟨i, hi⟩ := representatives_cover x
  have ho : orders i = 5 := (rep_orders i).symm.trans ((conj_order hi).trans hx)
  fin_cases i <;> norm_num [orders] at ho
  · exact hi.symm.trans (five_inverse.trans (conj_inv' hi))
  · exact hi.symm.trans (five_square_inverse.trans (conj_inv' hi))

theorem order_five_not_square (x : A6) (hx : orderOf x = 5) : ¬ IsConj x (x ^ 2) := by
  obtain ⟨i, hi⟩ := representatives_cover x
  have ho : orders i = 5 := (rep_orders i).symm.trans ((conj_order hi).trans hx)
  intro hc
  have hh := hi.trans (hc.trans (IsConj.pow 2 hi.symm))
  fin_cases i <;> norm_num [orders] at ho
  · exact five_nonsquare hh
  · exact five_square_nonsquare hh

end AlternatingSix.GoldenClassGeometry
