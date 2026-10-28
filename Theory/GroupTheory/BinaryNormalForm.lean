module

public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Counting a subgroup by binary normal forms

An ordered product of `n` optional generators has `2^n` possible bit strings.
If these products are distinct and their range is closed under division, that
range is a subgroup of order `2^n`. Lagrange then gives divisibility of the
ambient order. No commutativity or exponent-two assumption is imposed.

This is the elementary normal-form counting argument for a polycyclic
two-group. Concrete collection identities and separation of normal forms are
separate obligations; distinct elements alone do not imply divisibility.
-/

@[expose] public section

namespace Subgroup.BinaryNormalForm

variable {G : Type*} [Group G] {n : ℕ}

/-- Ordered product, with earlier indices on the left. -/
def product (g : Fin n → G) (v : Fin n → Bool) : G :=
  (List.ofFn (fun i => if v i then g i else 1)).prod

@[simp] theorem product_zero (g : Fin n → G) :
    product g (fun _ => false) = 1 := by
  simp [product]

theorem product_mem (g : Fin n → G) (v : Fin n → Bool)
    (H : Subgroup G) (hg : ∀ i, g i ∈ H) : product g v ∈ H := by
  apply H.list_prod_mem
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  split_ifs
  · exact hg i
  · exact H.one_mem

/-- The collection obligation, independent of uniqueness of normal forms. -/
def DivisionClosed (g : Fin n → G) : Prop :=
  ∀ v w, ∃ u, product g u = product g v * (product g w)⁻¹

/-- In a finite ambient group it suffices to collect a single generator on
the right. Positive words also represent inverses, so a separate inverse
collection table is unnecessary. -/
theorem divisionClosed_of_mul_generator [Finite G] (g : Fin n → G)
    (hstep : ∀ v i, ∃ w, product g w = product g v * g i) : DivisionClosed g := by
  have hnormal (x : G) (hx : x ∈ Subgroup.closure (Set.range g)) :
      ∃ v, product g v = x := by
    change x ∈ (Subgroup.closure (Set.range g)).toSubmonoid at hx
    rw [Subgroup.closure_toSubmonoid_of_finite] at hx
    induction hx using Submonoid.closure_induction_right with
    | one => exact ⟨_, product_zero g⟩
    | mul_right x hx y hy ih =>
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨v, rfl⟩ := ih
      exact hstep v i
  intro v w
  apply hnormal
  exact (Subgroup.closure (Set.range g)).mul_mem
    (product_mem g v _ (fun i => Subgroup.subset_closure (Set.mem_range_self i)))
    ((Subgroup.closure (Set.range g)).inv_mem
      (product_mem g w _ (fun i => Subgroup.subset_closure (Set.mem_range_self i))))

/-- A division-closed range of binary products is an actual subgroup. -/
def subgroup (g : Fin n → G) (h : DivisionClosed g) : Subgroup G :=
  Subgroup.ofDiv (Set.range (product g))
    ⟨product g (fun _ => false), Set.mem_range_self _⟩ (by
      rintro x ⟨v, rfl⟩ y ⟨w, rfl⟩
      exact h v w)

theorem card_subgroup (g : Fin n → G) (h : DivisionClosed g)
    (hinj : Function.Injective (product g)) : Nat.card (subgroup g h) = 2 ^ n := by
  change Nat.card (Set.range (product g)) = 2 ^ n
  rw [Nat.card_range_of_injective hinj]
  simp [Nat.card_eq_fintype_card]

/-- Collection and uniqueness together, rather than a mere lower bound,
certify the full power of two as a divisor. -/
theorem pow_dvd_card (g : Fin n → G) (h : DivisionClosed g)
    (hinj : Function.Injective (product g)) : 2 ^ n ∣ Nat.card G := by
  rw [← card_subgroup g h hinj]
  exact Subgroup.card_subgroup_dvd_card (subgroup g h)

end Subgroup.BinaryNormalForm
