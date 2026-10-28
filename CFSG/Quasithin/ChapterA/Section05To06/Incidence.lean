module

public import CFSG.Quasithin.ChapterA.Section05To06.Counting
public import Theory.GroupTheory.ConjugacyOrderCensus

/-!
# Incidence identities for the two involution classes

A.6.3 follows by counting commuting mixed-class pairs with product in one
specified involution class. Conjugation identifies the fibers over each
coordinate, and exchanging coordinates equates the two counts. The ordinary
conjugacy-class/centralizer cardinality formula clears the denominators.

Under the closure hypothesis of A.6.5, multiplication by `t` exchanges the
conjugates of `z` commuting with `t` and the nonexceptional part of `B2 t`.
The singleton `{t}` accounts for the extra one. Similarly, adjoining `{z}`
to `B1 z` gives all conjugates of `z` commuting with `z`. These arguments use
neither A.6.2 nor Thompson's order formula.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.6.3 and the
cardinality identities in the proof of A.6.5, printed pp. 64–65.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.ChapterA.Section05To06
variable {G : Type*} [Group G]

private theorem conj_order {a b : G} (h : IsConj a b) : orderOf a = orderOf b := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq a).symm

private theorem square {x : G} (h : orderOf x = 2) : x * x = 1 := by
  have he := pow_orderOf_eq_one x
  simpa only [h, pow_two] using he

private theorem nonone {x : G} (h : orderOf x = 2) : x ≠ 1 := by
  intro he; simp [he] at h

private theorem prod_nonone {x y : G} (hx : orderOf x = 2) (hn : x ≠ y) :
    x * y ≠ 1 := by
  intro he
  apply hn
  calc
    x = x * (x * y) := by rw [he, mul_one]
    _ = y := by rw [← mul_assoc, square hx, one_mul]

private theorem prod_order {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hc : Commute x y) (hn : x ≠ y) : orderOf (x * y) = 2 := by
  apply orderOf_eq_prime _ (prod_nonone hx hn)
  rw [hc.mul_pow, pow_two, pow_two, square hx, square hy, one_mul]

private theorem conj_iff (g z a : G) :
    IsConj z (MulAut.conj g a) ↔ IsConj z a := by
  have h : IsConj a (MulAut.conj g a) := isConj_iff.mpr ⟨g, rfl⟩
  exact ⟨fun h' => h'.trans h.symm, fun h' => h'.trans h⟩

private abbrev ProductFiber (y w x : G) :=
  {u : G // IsConj y u ∧ Commute u x ∧ IsConj w (u * x)}

private def productFiberConj (y w g x : G) :
    ProductFiber y w x ≃ ProductFiber y w (MulAut.conj g x) := by
  apply Equiv.subtypeEquiv (MulAut.conj g).toEquiv
  intro u
  change (_ ∧ _ ∧ _) ↔ (IsConj y (MulAut.conj g u) ∧
    Commute (MulAut.conj g u) (MulAut.conj g x) ∧
    IsConj w (MulAut.conj g u * MulAut.conj g x))
  rw [← map_mul, conj_iff, conj_iff]
  exact and_congr_right fun _ => and_congr_left fun _ =>
    ⟨fun h => h.map _, fun h => h.of_map (MulAut.conj g).injective⟩

private abbrev IncidencePairs (x y w : G) :=
  {p : G × G // IsConj x p.1 ∧ IsConj y p.2 ∧
    Commute p.2 p.1 ∧ IsConj w (p.2 * p.1)}

private def incidenceFiberEquiv (x y w : G) :
    (Σ u : {u : G // IsConj x u}, ProductFiber y w u.val) ≃ IncidencePairs x y w where
  toFun p := ⟨(p.1.val, p.2.val), p.1.property, p.2.property⟩
  invFun p := ⟨⟨p.val.1, p.property.1⟩, ⟨p.val.2, p.property.2⟩⟩
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

private theorem incidence_card [Finite G] (x y w : G) :
    Nat.card (IncidencePairs x y w) =
      Nat.card {u : G // IsConj x u} * Nat.card (ProductFiber y w x) := by
  classical
  let : Fintype {u : G // IsConj x u} := Fintype.ofFinite _
  rw [← Nat.card_congr (incidenceFiberEquiv x y w), Nat.card_sigma]
  have hf (u : {u : G // IsConj x u}) :
      Nat.card (ProductFiber y w u.val) = Nat.card (ProductFiber y w x) := by
    obtain ⟨g, hg⟩ := isConj_iff.mp u.property
    rw [← hg]
    exact (Nat.card_congr (productFiberConj y w g x)).symm
  simp only [hf, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card, Nat.cast_id]

private def incidenceSwap (x y w : G) : IncidencePairs x y w ≃ IncidencePairs y x w where
  toFun p := ⟨p.val.swap, p.property.2.1, p.property.1,
    p.property.2.2.1.symm, p.property.2.2.1.eq ▸ p.property.2.2.2⟩
  invFun p := ⟨p.val.swap, p.property.2.1, p.property.1,
    p.property.2.2.1.symm, p.property.2.2.1.eq ▸ p.property.2.2.2⟩
  left_inv := by intro p; rfl
  right_inv := by intro p; rfl

private theorem incidence_balance [Finite G] (x y w : G) :
    Nat.card (centralizer ({x} : Set G)) * Nat.card (ProductFiber x w y) =
      Nat.card (centralizer ({y} : Set G)) * Nat.card (ProductFiber y w x) := by
  have he := Nat.card_congr (incidenceSwap x y w)
  rw [incidence_card, incidence_card] at he
  have hx : Nat.card {u : G // IsConj x u} * Nat.card (centralizer ({x} : Set G)) =
      Nat.card G := ConjClasses.nat_card_carrier_mul_card_centralizer x
  have hy : Nat.card {u : G // IsConj y u} * Nat.card (centralizer ({y} : Set G)) =
      Nat.card G := ConjClasses.nat_card_carrier_mul_card_centralizer y
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := G))
  calc
    _ = (Nat.card {u : G // IsConj y u} * Nat.card (ProductFiber x w y)) *
        (Nat.card (centralizer ({x} : Set G)) * Nat.card (centralizer ({y} : Set G))) := by
      rw [← hy]; ring
    _ = (Nat.card {u : G // IsConj x u} * Nat.card (ProductFiber y w x)) *
        (Nat.card (centralizer ({x} : Set G)) * Nat.card (centralizer ({y} : Set G))) := by rw [he]
    _ = _ := by rw [← hx]; ring

private theorem fiber_c1 (x y : G) : Nat.card (ProductFiber y y x) = c1 x y := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro u
  change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  exact and_congr_right fun hu => and_congr_right fun _ =>
    ⟨fun hp => hu.symm.trans hp, fun hp => hu.trans hp⟩

private theorem fiber_c2 {z t : G} (h : TwoInvolutionClasses z t) :
    Nat.card (ProductFiber z t t) = c2 t z := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro u
  change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  refine and_congr_right fun hu => and_congr_right fun hc => ?_
  constructor
  · intro hp hn
    exact h.distinct (hu.trans (hn.trans hp.symm))
  · intro hn
    have hou : orderOf u = 2 := (conj_order hu).symm.trans h.order_z
    have hne : u ≠ t := fun he => h.distinct (he ▸ hu)
    rcases h.exhaustive (u * t) (prod_order hou h.order_t hc hne) with hp | hp
    · exact False.elim (hn (hu.symm.trans hp))
    · exact hp

private theorem classes_swap {z t : G} (h : TwoInvolutionClasses z t) :
    TwoInvolutionClasses t z :=
  ⟨h.order_t, h.order_z, fun he => h.distinct he.symm,
    fun x hx => (h.exhaustive x hx).symm⟩

/-- A.6.3, in fraction-free form, obtained by counting actual commuting
mixed pairs with product in each of the two involution classes. -/
theorem lemma_A_6_3 [Finite G] {z t : G} (h : TwoInvolutionClasses z t) :
    Nat.card (centralizer ({z} : Set G)) * c1 t z =
        Nat.card (centralizer ({t} : Set G)) * c2 z t ∧
    Nat.card (centralizer ({z} : Set G)) * c2 t z =
        Nat.card (centralizer ({t} : Set G)) * c1 z t := by
  constructor
  · simpa only [fiber_c1, fiber_c2 (classes_swap h)] using incidence_balance z t z
  · simpa only [fiber_c1, fiber_c2 h] using incidence_balance z t t

variable {z t : G}
variable (h : TwoInvolutionClasses z t)
variable (closed : ∀ u v : G, IsConj z u → IsConj z v → Commute u v →
  u * v ≠ 1 → IsConj z (u * v))
include h closed

private theorem mixed_product_not_z {u : G} (hu : IsConj z u) (hc : Commute u t) :
    ¬ IsConj z (u * t) := by
  intro hp
  have hou : orderOf u = 2 := (conj_order hu).symm.trans h.order_z
  have he : u * (u * t) = t := by rw [← mul_assoc, square hou, one_mul]
  have hh := closed u (u * t) hu hp ((Commute.refl u).mul_right hc)
    (by rw [he]; exact nonone h.order_t)
  exact h.distinct (he ▸ hh)

/-- Under the closure hypothesis of A.6.5 the first mixed counting set is empty. -/
theorem c1_eq_zero_of_closed [Finite G] : c1 t z = 0 := by
  have hempty : C1 t z = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro u hu
    exact mixed_product_not_z h closed hu.1 hu.2.1 (hu.1.trans hu.2.2)
  unfold c1
  rw [hempty]
  simp

/-- Under the closure hypothesis all conjugates of `z` commuting with `t`
lie in the second mixed counting set. -/
theorem c2_eq_card_of_closed [Finite G] :
    c2 t z = Nat.card {u : G // IsConj z u ∧ Commute u t} := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro u
  change (_ ∧ _ ∧ _) ↔ (_ ∧ _)
  exact ⟨fun hu => ⟨hu.1, hu.2.1⟩, fun hu =>
    ⟨hu.1, hu.2, fun hp => mixed_product_not_z h closed hu.1 hu.2 (hu.1.trans hp)⟩⟩

private theorem B1_union_singleton :
    B1 z ∪ {z} = {u : G | IsConj z u ∧ Commute u z} := by
  ext u
  constructor
  · rintro (hu | hu)
    · exact ⟨hu.1, hu.2.1⟩
    · have he : u = z := hu
      subst u
      exact ⟨IsConj.refl _, Commute.refl _⟩
  · intro hu
    by_cases he : u = z
    · exact Or.inr he
    · exact Or.inl ⟨hu.1, hu.2, hu.1.symm.trans
        (closed u z hu.1 (IsConj.refl _) hu.2
          (prod_nonone ((conj_order hu.1).symm.trans h.order_z) he))⟩
omit h closed in
private theorem self_not_B1 (x : G) (hx : orderOf x = 2) : x ∉ B1 x := by
  intro hm
  have he := conj_order hm.2.2
  rw [square hx, orderOf_one, hx] at he
  omega

/-- The sole missing conjugate of `z` in `B1 z` is `z` itself. -/
theorem b1_add_one_eq_card_of_closed [Finite G] :
    b1 z + 1 = Nat.card {u : G // IsConj z u ∧ Commute u z} := by
  classical
  have hd : Disjoint (B1 z) ({z} : Set G) := by
    rw [Set.disjoint_singleton_right]
    exact self_not_B1 z h.order_z
  have he := Nat.card_congr (Equiv.Set.union hd)
  rw [Nat.card_sum] at he
  rw [B1_union_singleton h closed] at he
  simpa only [b1, Nat.card_unique, Set.coe_ofPred] using he.symm

private theorem mixed_product_t {u : G} (hu : IsConj z u) (hc : Commute u t) :
    IsConj t (u * t) := by
  have hou : orderOf u = 2 := (conj_order hu).symm.trans h.order_z
  have hne : u ≠ t := fun he => h.distinct (he ▸ hu)
  exact (h.exhaustive (u * t) (prod_order hou h.order_t hc hne)).resolve_left
    (mixed_product_not_z h closed hu hc)

/-- Multiplication by `t` is the source bijection in A.6.5. Its domain
is the part of `B2 t` whose product with `t` belongs to the `z` class. -/
def closedClassMulEquiv :
    {u : G // IsConj t u ∧ Commute u t ∧ IsConj z (u * t)} ≃
      {u : G // IsConj z u ∧ Commute u t} where
  toFun u := ⟨u.val * t, u.property.2.2,
    u.property.2.1.mul_left (Commute.refl t)⟩
  invFun u := ⟨u.val * t, by exact mixed_product_t h closed u.property.1 u.property.2,
    u.property.2.mul_left (Commute.refl t),
    by simpa only [mul_assoc, square h.order_t, mul_one] using u.property.1⟩
  left_inv := by intro u; apply Subtype.ext; simp only [mul_assoc, square h.order_t, mul_one]
  right_inv := by intro u; apply Subtype.ext; simp only [mul_assoc, square h.order_t, mul_one]

omit closed in
private theorem B2_eq_union :
    B2 t = {u : G | IsConj t u ∧ Commute u t ∧ IsConj z (u * t)} ∪ {t} := by
  ext u
  constructor
  · intro hu
    by_cases he : u = t
    · exact Or.inr he
    · refine Or.inl ⟨hu.1, hu.2.1, ?_⟩
      have hou : orderOf u = 2 := (conj_order hu.1).symm.trans h.order_t
      rcases h.exhaustive (u * t) (prod_order hou h.order_t hu.2.1 he) with hp | hp
      · exact hp
      · exact False.elim (hu.2.2 (hu.1.symm.trans hp))
  · rintro (hu | hu)
    · exact ⟨hu.1, hu.2.1, fun hp => h.distinct (hu.2.2.trans (hp.symm.trans hu.1.symm))⟩
    · have he : u = t := hu
      subst u
      refine ⟨IsConj.refl _, Commute.refl _, ?_⟩
      intro hp
      have ho := conj_order hp
      rw [h.order_t, square h.order_t, orderOf_one] at ho
      omega

/-- The exceptional element `t` contributes one in the A.6.5 count of `B2 t`. -/
theorem b2_eq_card_add_one_of_closed [Finite G] :
    b2 t = Nat.card {u : G // IsConj z u ∧ Commute u t} + 1 := by
  classical
  have hd : Disjoint {u : G | IsConj t u ∧ Commute u t ∧ IsConj z (u * t)}
      ({t} : Set G) := by
    rw [Set.disjoint_singleton_right]
    intro ht
    have ho := conj_order ht.2.2
    rw [h.order_z, square h.order_t, orderOf_one] at ho
    omega
  unfold b2
  rw [B2_eq_union h, Nat.card_congr (Equiv.Set.union hd), Nat.card_sum,
    Set.coe_ofPred, Nat.card_congr (closedClassMulEquiv h closed)]
  simp only [Nat.card_unique]
end CFSG.Quasithin.ChapterA.Section05To06

end
