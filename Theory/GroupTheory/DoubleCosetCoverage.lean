module
public import Theory.GroupTheory.DoubleCosetCard
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting certificates for double-coset coverage

Pairwise disjoint double cosets cover a finite group when lower bounds on
their sizes sum to its order. Upper bounds on conjugate intersections suffice.
Invariant-set intersection counts provide a structural separation test.

Source application: the Sylow-overgroup calculation in Aschbacher--Smith
A.3.12(18), printed pp.47--48; the counting argument is elementary.
-/

public section
open Subgroup DoubleCoset
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Disjoint double cosets whose certified lower sizes exhaust the ambient
order cover the group. Intersection upper bounds suffice. -/
theorem doubleCoset_cover_of_card_bound {n : ℕ} (S : Subgroup G)
    (d : Fin n → G) (lower bound : Fin n → ℕ)
    (hd : Pairwise fun i j => Disjoint (doubleCoset (d i) S S) (doubleCoset (d j) S S))
    (hb : ∀ i, Nat.card (S ⊓ S.map (MulAut.conj (d i)).toMonoidHom : Subgroup G) ≤ bound i)
    (hpos : ∀ i, 0 < bound i)
    (hmul : ∀ i, lower i * bound i = Nat.card S * Nat.card S)
    (hsum : Nat.card G ≤ ∑ i, lower i) :
    ∀ g : G, ∃ i, g ∈ doubleCoset (d i) S S := by
  classical
  let f : (i : Fin n) × doubleCoset (d i) S S → G := fun x => x.2.val
  have hf : Function.Injective f := by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    change x.val = y.val at h
    have hij : i = j := by
      by_contra hn
      exact Set.disjoint_left.mp (hd hn) x.property (h.symm ▸ y.property)
    subst j
    exact congrArg (Sigma.mk i) (Subtype.ext h)
  have hc : ∀ i, lower i ≤ Nat.card (doubleCoset (d i) S S) := by
    intro i
    have h := card_doubleCoset_mul_card_inf S S (d i)
    have hle := Nat.mul_le_mul_left (Nat.card (doubleCoset (d i) S S)) (hb i)
    rw [h, ← hmul i] at hle
    exact Nat.le_of_mul_le_mul_right hle (hpos i)
  have hcard : Nat.card G ≤ Nat.card ((i : Fin n) × doubleCoset (d i) S S) := by
    rw [Nat.card_sigma]
    exact hsum.trans (Finset.sum_le_sum (fun i _ => hc i))
  intro g
  obtain ⟨⟨i,x⟩,hx⟩ := (hf.bijective_of_nat_card_le hcard).surjective g
  exact ⟨i,hx ▸ x.property⟩

variable {Ω : Type*}
/-- Counts with an invariant colour are constant on double cosets. -/
theorem filter_card_perm_mul_of_color (B : Finset Ω) (color : Ω → ℕ) (v : ℕ)
    (g a b : Equiv.Perm Ω)
    (ha : ∀ x, color (a x) = color x) (hb : ∀ x, b x ∈ B ↔ x ∈ B) :
    (B.filter fun x => color ((a * g * b) x) = v).card =
      (B.filter fun x => color (g x) = v).card := by
  apply Finset.card_bij (fun x _ => b x)
  · intro x hx
    obtain ⟨hx, hg⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨(hb x).mpr hx,(ha (g (b x))) ▸ hg⟩
  · intro x hx y hy h
    exact b.injective h
  · intro y hy
    refine ⟨b.symm y, ?_, b.apply_symm_apply y⟩
    obtain ⟨hy,hg⟩ := Finset.mem_filter.mp hy
    apply Finset.mem_filter.mpr
    constructor
    · exact (hb (b.symm y)).mp (by simpa using hy)
    · change color (a (g (b (b.symm y)))) = v
      rw [b.apply_symm_apply,ha]
      exact hg

end Theory.GroupTheory
