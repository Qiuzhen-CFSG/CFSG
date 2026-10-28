module

public import Theory.GroupTheory.DihedralHalfOrderClasses
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Local fibers for the two-involution-class order estimate

The product slices record ambient classes inside full centralizers. The
half-order fiber splits according to the product order modulo four. In the
second part, the two transformed factors are conjugate inside the full
centralizer, giving a bound by pairs in the same local conjugacy class.

Source motivation: Aschbacher–Smith, A.6.1–4, printed pp. 64–65.
-/

@[expose] public section
namespace Theory.GroupTheory.TwoInvolutionClassLocalBounds
open TwoInvolutionClassOrder
open scoped BigOperators
variable {G : Type*} [Group G]

/-- The full centralizer of a marked element. -/
abbrev Centralizer (x : G) := Subgroup.centralizer ({x} : Set G)

/-- Elements of the `a` class whose product with the mark lies in the `b` class. -/
abbrev Slice (x a b : G) :=
  {u : Centralizer x // IsConj a (u : G) ∧ IsConj b ((u : G) * x)}

/-- Pairs in a product slice conjugate inside the full centralizer. -/
abbrev SameOrbit (x a b : G) :=
  {p : Slice x a b × Slice x a b // IsConj p.1.val p.2.val}

/-- A conjugacy class in the full centralizer, without any ambient fusion assumption. -/
abbrev LocalOrbit {x : G} (u : Centralizer x) :=
  {v : Centralizer x // IsConj u v}

private theorem conj_order {a b : G} (h : IsConj a b) : orderOf a = orderOf b := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq a).symm

private theorem square {x : G} (hx : orderOf x = 2) : x * x = 1 := by
  simpa only [hx, pow_two] using pow_orderOf_eq_one x

private abbrev Part (z t x : G) (k : ℕ) :=
  {p : Fiber z t x // orderOf (p.val.1 * p.val.2) % 4 = k}

private theorem fiber_split [Finite G] {z t x : G}
    (hz : orderOf z = 2) (ht : orderOf t = 2) (hn : ¬ IsConj z t) :
    kappa z t x = Nat.card (Part z t x 0) + Nat.card (Part z t x 2) := by
  classical
  have hm (p : Fiber z t x) : orderOf (p.val.1 * p.val.2) % 4 = 0 ∨
      orderOf (p.val.1 * p.val.2) % 4 = 2 := by
    have hp := (halfOrder_properties hz ht hn p.property.1 p.property.2.1).1
    have hd := orderOf_pow_dvd (x := p.val.1 * p.val.2)
      (orderOf (p.val.1 * p.val.2) / 2)
    rw [← halfOrder_def, hp] at hd
    omega
  have hi (p : Fiber z t x) :
      (¬ orderOf (p.val.1 * p.val.2) % 4 = 0) ↔
        orderOf (p.val.1 * p.val.2) % 4 = 2 := by
    have := hm p
    omega
  have he := Nat.card_congr (Equiv.sumCompl
    (fun p : Fiber z t x => orderOf (p.val.1 * p.val.2) % 4 = 0))
  rw [Nat.card_sum, Nat.card_congr (Equiv.subtypeEquivRight hi)] at he
  rw [kappa_def]
  simpa only [Fiber, halfOrder_def] using he.symm

private theorem part_zero_bound [Finite G] {z t x : G}
    (hz : orderOf z = 2) (ht : orderOf t = 2) (hn : ¬ IsConj z t) :
    Nat.card (Part z t x 0) ≤ Nat.card (Slice x z z) * Nat.card (Slice x t t) := by
  let f : Part z t x 0 → Slice x z z × Slice x t t := fun p => by
    have hc := fiber_mem_centralizer hz ht hn p.val
    have hr := DihedralHalfOrderClasses.preserve
      ((conj_order p.val.property.1).symm.trans hz)
      ((conj_order p.val.property.2.1).symm.trans ht) p.property
    rw [p.val.property.2.2] at hr
    exact (⟨⟨p.val.val.1, hc.1⟩, p.val.property.1, p.val.property.1.trans hr.1⟩,
      ⟨⟨p.val.val.2, hc.2⟩, p.val.property.2.1, p.val.property.2.1.trans hr.2⟩)
  rw [← Nat.card_prod]
  apply Nat.card_le_card_of_injective f
  intro p q he
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (congrArg (fun v => v.1.val.val) he)
    (congrArg (fun v => v.2.val.val) he)

/-- The exchange conjugator lies in the full centralizer: apply the dihedral
lemma to the lifted factors there, and only then forget to the ambient group. -/
theorem exchange_in_centralizer [Finite G] {z t x : G}
    (hz : orderOf z = 2) (ht : orderOf t = 2) (hn : ¬ IsConj z t)
    (p : Fiber z t x) (hm : orderOf (p.val.1 * p.val.2) % 4 = 2) :
    let hc := fiber_mem_centralizer hz ht hn p
    let a : Centralizer x := ⟨p.val.1, hc.1⟩
    let b : Centralizer x := ⟨p.val.2, hc.2⟩
    let mark : Centralizer x := ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    IsConj b (a * mark) ∧ IsConj a (b * mark) := by
  dsimp only
  let hc := fiber_mem_centralizer hz ht hn p
  let a : Centralizer x := ⟨p.val.1, hc.1⟩
  let b : Centralizer x := ⟨p.val.2, hc.2⟩
  let mark : Centralizer x := ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have he : halfOrder a b = mark := by
    apply Subtype.ext
    exact (halfOrder_coe _ a b).trans p.property.2.2
  have ha : orderOf a = 2 :=
    (Subgroup.orderOf_coe a).symm.trans ((conj_order p.property.1).symm.trans hz)
  have hb : orderOf b = 2 :=
    (Subgroup.orderOf_coe b).symm.trans ((conj_order p.property.2.1).symm.trans ht)
  have hm' : orderOf (a * b) % 4 = 2 := by
    rw [← Subgroup.orderOf_coe]; exact hm
  simpa only [he] using DihedralHalfOrderClasses.exchange ha hb hm'

private theorem part_two_bound [Finite G] {z t x : G}
    (hz : orderOf z = 2) (ht : orderOf t = 2) (hn : ¬ IsConj z t)
    (hx : orderOf x = 2) : Nat.card (Part z t x 2) ≤ Nat.card (SameOrbit x t z) := by
  let f : Part z t x 2 → SameOrbit x t z := fun p => by
    have hc := fiber_mem_centralizer hz ht hn p.val
    let a : Centralizer x := ⟨p.val.val.1, hc.1⟩
    let b : Centralizer x := ⟨p.val.val.2, hc.2⟩
    let mark : Centralizer x := ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have hr : IsConj b (a * mark) ∧ IsConj a (b * mark) :=
      exchange_in_centralizer hz ht hn p.val p.property
    have hr1 := (Centralizer x).subtype.map_isConj hr.1
    have hr2 := (Centralizer x).subtype.map_isConj hr.2
    refine ⟨(⟨b, p.val.property.2.1, p.val.property.1.trans hr2⟩,
      ⟨a * mark, p.val.property.2.1.trans hr1, ?_⟩), hr.1⟩
    change IsConj z ((p.val.val.1 * x) * x)
    simpa only [mul_assoc, square hx, mul_one] using p.val.property.1
  apply Nat.card_le_card_of_injective f
  intro p q he
  apply Subtype.ext
  apply Subtype.ext
  have h1 := congrArg (fun v : SameOrbit x t z => v.val.2.val.val) he
  have h2 := congrArg (fun v : SameOrbit x t z => v.val.1.val.val) he
  exact Prod.ext (mul_right_cancel h1) h2

/-- A refined Thompson fiber bound retaining conjugacy inside the centralizer. -/
theorem kappa_le_local [Finite G] {z t x : G}
    (hz : orderOf z = 2) (ht : orderOf t = 2) (hn : ¬ IsConj z t)
    (hx : orderOf x = 2) :
    kappa z t x ≤ Nat.card (Slice x z z) * Nat.card (Slice x t t) +
      Nat.card (SameOrbit x t z) := by
  rw [fiber_split hz ht hn]
  exact Nat.add_le_add (part_zero_bound hz ht hn) (part_two_bound hz ht hn hx)

/-- Forgetting the local conjugacy condition bounds the count by a square. -/
theorem sameOrbit_card_le_square [Finite G] (x a b : G) :
    Nat.card (SameOrbit x a b) ≤ Nat.card (Slice x a b) ^ 2 := by
  simpa only [Nat.card_prod, pow_two] using
    Nat.card_le_card_of_injective (Subtype.val : SameOrbit x a b → _)
      Subtype.val_injective

/-- Covering a finite set by classes need not be disjoint. -/
theorem slice_card_le_sum [Finite G] {ι : Type*} [Fintype ι] {x a b : G}
    (w : ι → Centralizer x) (n : ι → ℕ)
    (hcover : ∀ u : Slice x a b, ∃ i, IsConj (w i) u.val)
    (hbound : ∀ i, Nat.card (LocalOrbit (w i)) ≤ n i) :
    Nat.card (Slice x a b) ≤ ∑ i, n i := by
  classical
  let f : Slice x a b → Σ i, LocalOrbit (w i) := fun u =>
    ⟨(hcover u).choose, u.val, (hcover u).choose_spec⟩
  have hf : Function.Injective f := by
    intro u v he
    exact Subtype.ext (congrArg (fun p => p.2.val) he)
  exact (Nat.card_le_card_of_injective f hf).trans
    (Nat.card_sigma.trans_le (Finset.sum_le_sum fun i _ => hbound i))

/-- A cover by local classes bounds same-class ordered pairs by a sum of squares.
Overlaps only overcount, and representatives need not be separated. -/
theorem sameOrbit_card_le_sum_sq [Finite G] {ι : Type*} [Fintype ι] {x a b : G}
    (w : ι → Centralizer x) (n : ι → ℕ)
    (hcover : ∀ u : Slice x a b, ∃ i, IsConj (w i) u.val)
    (hbound : ∀ i, Nat.card (LocalOrbit (w i)) ≤ n i) :
    Nat.card (SameOrbit x a b) ≤ ∑ i, (n i)^2 := by
  classical
  let f : SameOrbit x a b → Σ i, LocalOrbit (w i) × LocalOrbit (w i) := fun p =>
    ⟨(hcover p.val.1).choose,
      ⟨p.val.1.val, (hcover p.val.1).choose_spec⟩,
      ⟨p.val.2.val, (hcover p.val.1).choose_spec.trans p.property⟩⟩
  have hf : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    exact Prod.ext
      (Subtype.ext (congrArg (fun s => s.2.1.val) he))
      (Subtype.ext (congrArg (fun s => s.2.2.val) he))
  refine (Nat.card_le_card_of_injective f hf).trans ?_
  rw [Nat.card_sigma]
  apply Finset.sum_le_sum
  intro i _
  rw [Nat.card_prod, pow_two]
  exact Nat.mul_le_mul (hbound i) (hbound i)

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
    Nat.card (Subgroup.centralizer ({x} : Set G)) * Nat.card (ProductFiber x w y) =
      Nat.card (Subgroup.centralizer ({y} : Set G)) * Nat.card (ProductFiber y w x) := by
  have he := Nat.card_congr (incidenceSwap x y w)
  rw [incidence_card, incidence_card] at he
  have hx : Nat.card {u : G // IsConj x u} * Nat.card (Subgroup.centralizer ({x} : Set G)) =
      Nat.card G := ConjClasses.nat_card_carrier_mul_card_centralizer x
  have hy : Nat.card {u : G // IsConj y u} * Nat.card (Subgroup.centralizer ({y} : Set G)) =
      Nat.card G := ConjClasses.nat_card_carrier_mul_card_centralizer y
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := G))
  calc
    _ = (Nat.card {u : G // IsConj y u} * Nat.card (ProductFiber x w y)) *
        (Nat.card (Subgroup.centralizer ({x} : Set G)) * Nat.card (Subgroup.centralizer ({y} : Set G))) := by
      rw [← hy]; ring
    _ = (Nat.card {u : G // IsConj x u} * Nat.card (ProductFiber y w x)) *
        (Nat.card (Subgroup.centralizer ({x} : Set G)) * Nat.card (Subgroup.centralizer ({y} : Set G))) := by rw [he]
    _ = _ := by rw [← hx]; ring

/-- Removing the redundant centralizer subtype gives the ordinary commuting fiber. -/
private def sliceEquivProductFiber (x a b : G) : Slice x a b ≃ ProductFiber a b x where
  toFun u := ⟨u.val.val, u.property.1,
    Subgroup.mem_centralizer_singleton_iff.mp u.val.property, u.property.2⟩
  invFun u := ⟨⟨u.val, Subgroup.mem_centralizer_singleton_iff.mpr u.property.2.1.eq⟩,
    u.property.1, u.property.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Count commuting marked pairs with product in a specified ambient class. -/
theorem slice_incidence_balance [Finite G] (x y b : G) :
    Nat.card (Centralizer x) * Nat.card (Slice y x b) =
      Nat.card (Centralizer y) * Nat.card (Slice x y b) := by
  rw [Nat.card_congr (sliceEquivProductFiber y x b),
    Nat.card_congr (sliceEquivProductFiber x y b)]
  exact incidence_balance x y b

/-- The centralizer ratio transports the mixed slice bound without division. -/
theorem slice_card_le_of_ratio [Finite G] {z t : G} {r d : ℕ}
    (hr : 0 < r) (hcard : Nat.card (Centralizer z) = r * Nat.card (Centralizer t))
    (hY : Nat.card (Slice z t z) ≤ r * d) :
    Nat.card (Slice t z z) ≤ d := by
  have he := slice_incidence_balance z t z
  rw [hcard] at he
  have hmul : r * Nat.card (Slice t z z) = Nat.card (Slice z t z) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Centralizer t))
    calc
      _ = (r * Nat.card (Centralizer t)) * Nat.card (Slice t z z) := by ring
      _ = _ := he
  exact Nat.le_of_mul_le_mul_left (hmul.trans_le hY) hr

/-- The local same-class slice is bounded by all elements of that ambient class. -/
theorem slice_card_le_class_count [Finite G] (x a b : G) :
    Nat.card (Slice x a b) ≤ Nat.card {u : Centralizer x // IsConj a (u : G)} := by
  exact Nat.card_le_card_of_injective
    (fun u : Slice x a b => (⟨u.val, u.property.1⟩ : {u : Centralizer x // IsConj a (u : G)}))
    (fun u v he => Subtype.ext (congrArg (fun q : {u : Centralizer x // IsConj a (u : G)} => q.val) he))

/-- Arithmetic assembly of the refined order estimate. The cover in `C(t)`
is explicit here; transporting it from `C(z)` is a separate geometric step. -/
theorem card_le_of_two_local_covers [Finite G] {ι : Type*} [Fintype ι]
    (z t : G) (hz : orderOf z = 2) (ht : orderOf t = 2) (hn : ¬ IsConj z t)
    (hclasses : ∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj t u)
    (r bz bt d : ℕ) (n : ι → ℕ) (hr : 0 < r)
    (hcard : Nat.card (Centralizer z) = r * Nat.card (Centralizer t))
    (hX : Nat.card (Slice z z z) ≤ bz)
    (hY : Nat.card (Slice z t z) ≤ r * d)
    (htcount : Nat.card {u : Centralizer t // IsConj t (u : G)} ≤ bt)
    (w : ι → Centralizer z)
    (hwcover : ∀ u : Slice z t t, ∃ i, IsConj (w i) u.val)
    (hwbound : ∀ i, Nat.card (LocalOrbit (w i)) ≤ r * n i)
    (v : ι → Centralizer t)
    (hvcover : ∀ u : Slice t t z, ∃ i, IsConj (v i) u.val)
    (hvbound : ∀ i, Nat.card (LocalOrbit (v i)) ≤ n i) :
    Nat.card G ≤ Nat.card (Centralizer t) *
      (bz * (r * ∑ i, n i) + (r*d+1)*(r*d) + r*(bt*d + ∑ i, (n i)^2)) := by
  have hW : Nat.card (Slice z t t) ≤ r * ∑ i, n i := by
    simpa only [Finset.mul_sum] using slice_card_le_sum w (fun i => r * n i) hwcover hwbound
  have hD := sameOrbit_card_le_sum_sq v n hvcover hvbound
  have hC := slice_card_le_of_ratio hr hcard hY
  have hB := (slice_card_le_class_count t t t).trans htcount
  have hkz : kappa z t z ≤ bz * (r * ∑ i, n i) + (r*d+1)*(r*d) := by
    refine (kappa_le_local hz ht hn hz).trans (Nat.add_le_add (Nat.mul_le_mul hX hW) ?_)
    have hsq := (sameOrbit_card_le_square z t z).trans (Nat.pow_le_pow_left hY 2)
    exact hsq.trans (by nlinarith)
  have hkt : kappa z t t ≤ bt*d + ∑ i, (n i)^2 := by
    refine (kappa_le_local hz ht hn ht).trans ?_
    exact Nat.add_le_add (by simpa only [Nat.mul_comm] using Nat.mul_le_mul hC hB) hD
  rw [TwoInvolutionClassOrder.card_eq z t hz ht hn hclasses, hcard]
  calc
    _ ≤ (bz * (r * ∑ i, n i) + (r*d+1)*(r*d)) * Nat.card (Centralizer t) +
        (bt*d + ∑ i, (n i)^2) * (r * Nat.card (Centralizer t)) :=
      Nat.add_le_add (Nat.mul_le_mul_right _ hkz) (Nat.mul_le_mul_right _ hkt)
    _ = _ := by ring

end Theory.GroupTheory.TwoInvolutionClassLocalBounds
end
