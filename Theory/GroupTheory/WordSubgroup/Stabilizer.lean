module

public import Theory.GroupTheory.WordSubgroup
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Stabilizer upper bounds from Schreier transitions

Suppose every generator times a representative reduces to a representative
times an element of `K`. Induction on words gives this decomposition for the
whole word subgroup. If `K` fixes the base point, and only the identity
representative fixes it, every element of the base-point stabilizer lies in `K`.

The transition equations must hold in the actual permutation group. No order
table, claimed strong generating set, or external stabilizer computation is
assumed. This is the stabilizer part of the Schreier rewriting argument used
by `wordSubgroup_card_eq_mul_next`, without its unnecessary lower-bound data.
-/

namespace Theory.GroupTheory

/-- A Schreier transition certificate bounds the stabilizer in a subgroup
given by `Subgroup.closure`. Both generator directions are checked explicitly,
so no order or inverse-generator certificate is needed. -/
public theorem closure_stabilizer_le_next {V ι : Type*}
    (generators : Set (Equiv.Perm V)) (K : Subgroup (Equiv.Perm V))
    (rep : ι → Equiv.Perm V) (initial : ι) (base : V)
    (hInitial : rep initial = 1)
    (hStep : ∀ s ∈ generators, ∀ r, ∃ t, ∃ k : K, s * rep r = rep t * k.val)
    (hInvStep : ∀ s ∈ generators, ∀ r, ∃ t, ∃ k : K,
      s⁻¹ * rep r = rep t * k.val)
    (hFix : ∀ k : K, k.val base = base)
    (hSeparate : ∀ r, rep r base = base → rep r = 1)
    {g : Equiv.Perm V} (hg : g ∈ Subgroup.closure generators)
    (hbase : g base = base) : g ∈ K := by
  have decompose : ∃ r, ∃ k : K, g = rep r * k.val := by
    clear hbase
    induction hg using Subgroup.closure_induction_left with
    | one => exact ⟨initial, 1, by simp [hInitial]⟩
    | mul_left s hs g _ ih =>
      obtain ⟨r, k, hk⟩ := ih
      obtain ⟨t, l, hl⟩ := hStep s hs r
      refine ⟨t, l * k, ?_⟩
      change s * g = rep t * (l.val * k.val)
      rw [hk, ← mul_assoc, hl, mul_assoc]
    | inv_mul_cancel s hs g _ ih =>
      obtain ⟨r, k, hk⟩ := ih
      obtain ⟨t, l, hl⟩ := hInvStep s hs r
      refine ⟨t, l * k, ?_⟩
      change s⁻¹ * g = rep t * (l.val * k.val)
      rw [hk, ← mul_assoc, hl, mul_assoc]
  obtain ⟨r, k, hk⟩ := decompose
  have hr : rep r base = base := by
    simpa only [hk, Equiv.Perm.mul_apply, hFix] using hbase
  rw [hk, hSeparate r hr, one_mul]
  exact k.property

/-- Schreier transitions certify an upper bound for a point stabilizer.
Representatives need not be proved to lie in the generated subgroup, and `K`
need not be proved to be contained in it. These are upper bounds only. -/
public theorem wordSubgroup_stabilizer_le_next {V ι : Type*} {n : Nat}
    (gen : Fin n → Equiv.Perm V) (invOf : Fin n → Fin n)
    (hInv : ∀ i, gen (invOf i) = (gen i)⁻¹)
    (K : Subgroup (Equiv.Perm V))
    (rep : ι → Equiv.Perm V) (initial : ι) (base : V)
    (hInitial : rep initial = 1)
    (hStep : ∀ i r, ∃ s, ∃ k : K, gen i * rep r = rep s * k.val)
    (hFix : ∀ k : K, k.val base = base)
    (hSeparate : ∀ r, rep r base = base → rep r = 1)
    {g : Equiv.Perm V} (hg : g ∈ wordSubgroup gen invOf hInv)
    (hbase : g base = base) : g ∈ K := by
  have decompose : ∀ w : List (Fin n), ∃ r, ∃ k : K,
      evalWord gen w = rep r * k.val := by
    intro w
    induction w with
    | nil => exact ⟨initial, 1, by simp [evalWord, hInitial]⟩
    | cons i w ih =>
      obtain ⟨r, k, hk⟩ := ih
      obtain ⟨s, l, hl⟩ := hStep i r
      refine ⟨s, l * k, ?_⟩
      change gen i * evalWord gen w = rep s * (l.val * k.val)
      rw [hk, ← mul_assoc, hl, mul_assoc]
  obtain ⟨w, rfl⟩ := hg
  obtain ⟨r, k, hk⟩ := decompose w
  have hr : rep r base = base := by
    simpa only [hk, Equiv.Perm.mul_apply, hFix] using hbase
  rw [hk, hSeparate r hr, one_mul]
  exact k.property

end Theory.GroupTheory
