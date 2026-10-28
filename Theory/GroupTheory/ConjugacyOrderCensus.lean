module
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Fintype.BigOperators

/-!
# Actual conjugacy classes of elements of a fixed order

The finite set of classes of order `n` partitions the elements of order `n`.
Its sum of carrier cardinalities is therefore their cardinality. The class-size
formula is recorded with `Nat.card` and the ordinary subgroup centralizer.
-/
open scoped BigOperators
namespace ConjClasses
noncomputable section
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem order_eq_of_mk_eq {x y : G} (h : ConjClasses.mk x = ConjClasses.mk y) : orderOf x = orderOf y := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (mk_eq_mk_iff_isConj.mp h)
  rw [← hg]
  exact ((MulAut.conj g).orderOf_eq x).symm

/-- The actual conjugacy classes whose elements have order `n`. -/
public def ofOrder (G : Type*) [Group G] [Finite G] (n : ℕ) : Finset (ConjClasses G) := by
  classical
  let : Fintype G := Fintype.ofFinite _
  exact (Finset.univ.filter (fun x : G => orderOf x = n)).image ConjClasses.mk

/-- Membership in the order-class set is exactly the element-order condition. -/
@[simp] public theorem mk_mem_ofOrder (n : ℕ) (x : G) :
    ConjClasses.mk x ∈ ofOrder G n ↔ orderOf x = n := by
  classical
  simp only [ofOrder, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, hy, he⟩
    exact (order_eq_of_mk_eq he).symm.trans hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Every member of the order-class set has a representative of that order. -/
public theorem mem_ofOrder_iff (n : ℕ) (k : ConjClasses G) :
    k ∈ ofOrder G n ↔ ∃ x : G, ConjClasses.mk x = k ∧ orderOf x = n := by
  classical
  simp only [ofOrder, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact exists_congr fun _ => and_comm

/-- The carriers of the order classes partition the elements of that order. -/
public theorem sum_card_ofOrder (n : ℕ) :
    ∑ k ∈ ofOrder G n, Nat.card k.carrier = Nat.card {x : G // orderOf x = n} := by
  classical
  let f : (Σ k : ↥(ofOrder G n), k.val.carrier) → {x : G // orderOf x = n} := fun z =>
    ⟨z.2.val, (mk_mem_ofOrder n z.2.val).mp
      ((mem_carrier_iff_mk_eq.mp z.2.property).symm ▸ z.1.property)⟩
  have hinj : Function.Injective f := by
    rintro ⟨k, x⟩ ⟨l, y⟩ h
    have he : x.val = y.val := congrArg Subtype.val h
    have hkl : k = l := Subtype.ext ((mem_carrier_iff_mk_eq.mp x.property).symm.trans
      ((congrArg ConjClasses.mk he).trans (mem_carrier_iff_mk_eq.mp y.property)))
    subst l
    congr 1
    exact Subtype.ext he
  have hsurj : Function.Surjective f := by
    intro x
    exact ⟨⟨⟨ConjClasses.mk x.val, (mk_mem_ofOrder n x.val).mpr x.property⟩,
      ⟨x.val, mem_carrier_mk⟩⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_sigma]
  exact (Finset.sum_coe_sort (ofOrder G n) (fun k => Nat.card k.carrier)).symm

omit [Finite G] in
/-- A conjugacy class has cardinality equal to the centralizer index. -/
public theorem nat_card_carrier_mul_card_centralizer (x : G) :
    Nat.card (ConjClasses.mk x).carrier * Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card G := by
  have hstab : Nat.card (Subgroup.centralizer ({x} : Set G)) =
      Nat.card (MulAction.stabilizer (ConjAct G) x) := by
    rw [Subgroup.centralizer_eq_comap_stabilizer]
    rfl
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct G) x)
  rw [Nat.card_prod, ← hstab, ConjAct.orbit_eq_carrier_conjClasses] at hc
  exact hc

end
end ConjClasses
