module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic.Group

/-!
# The projection of an inner involution onto a component

In the centerless cases of Aschbacher–Smith 2.3.9(7)(d,g), the element
denoted z_L is the unique element of L inducing the action of z. Its order
is two, and its centralizer in L is exactly the fixed subgroup of z.
This module proves those assertions from the literal conjugation action.
It makes no assertion that this centralizer is maximal.

Source: combined manuscript of 1 March 2004, printed pp.525–526.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement

open Subgroup

variable {K : Type*} [Group K]

private theorem conj_ker : (MulAut.conj (G := K)).ker = center K := by
  ext g
  rw [MonoidHom.mem_ker, mem_center_iff]
  constructor
  · intro h x
    have he : g * x * g⁻¹ = x := DFunLike.congr_fun h x
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro h
    ext x
    change g * x * g⁻¹ = x
    rw [← h x, mul_inv_cancel_right]

/-- Centerlessness makes an inner automorphism's inducing element unique. -/
theorem conj_injective_of_center_eq_bot (hZ : center K = ⊥) :
    Function.Injective (MulAut.conj (G := K)) := by
  apply (MonoidHom.ker_eq_bot_iff (MulAut.conj (G := K))).mp
  rw [conj_ker, hZ]

/-- A nonidentity inner automorphism of order two has a unique involution
as its inducing element in a centerless group. -/
theorem exists_unique_inner_involution (hZ : center K = ⊥)
    (α : MulAut K) (hα : α ^ 2 = 1) (hne : α ≠ 1)
    (hinner : α ∈ (MulAut.conj (G := K)).range) :
    ∃! t : K, MulAut.conj t = α ∧ orderOf t = 2 := by
  obtain ⟨t, ht⟩ := hinner
  have hinj := conj_injective_of_center_eq_bot hZ
  have ht2 : t ^ 2 = 1 := hinj (by rw [map_pow, ht, hα, map_one])
  have htne : t ≠ 1 := by
    intro he
    apply hne
    rw [← ht, he, map_one]
  exact ⟨t, ⟨ht, orderOf_eq_prime ht2 htne⟩, fun u hu => hinj (hu.1.trans ht.symm)⟩

variable {G : Type*} [Group G]

/-- The literal meaning of z_L, without any ambient-normality requirement
on L and without choosing a noncanonical decomposition of z. -/
def IsConjugationProjection (L : Subgroup G) (z : G) (t : L) : Prop :=
  ∀ x : L, z * (x : G) * z⁻¹ = ((t * x * t⁻¹ : L) : G)

/-- Centralizers transfer to the inducing element of an inner action. -/
theorem centralizer_intersection_of_projection {L : Subgroup G} {z : G} {t : L}
    (ht : IsConjugationProjection L z t) :
    L ⊓ centralizer ({z} : Set G) = L ⊓ centralizer ({(t : G)} : Set G) := by
  ext x
  constructor
  · rintro ⟨hx, hxc⟩
    refine ⟨hx, mem_centralizer_singleton_iff.mpr ?_⟩
    have he := ht ⟨x, hx⟩
    change z * x * z⁻¹ = (t : G) * x * (t : G)⁻¹ at he
    rw [← mem_centralizer_singleton_iff.mp hxc, mul_inv_cancel_right] at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  · rintro ⟨hx, hxc⟩
    refine ⟨hx, mem_centralizer_singleton_iff.mpr ?_⟩
    have he := ht ⟨x, hx⟩
    change z * x * z⁻¹ = (t : G) * x * (t : G)⁻¹ at he
    rw [← mem_centralizer_singleton_iff.mp hxc, mul_inv_cancel_right] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The involution projection therefore supplies the lower containment
needed for the eventual model-specific overgroup argument. -/
theorem projection_centralizer_le_intersection {L M : Subgroup G} {z : G} {t : L}
    (ht : IsConjugationProjection L z t)
    (hCM : centralizer ({z} : Set G) ≤ M) :
    L ⊓ centralizer ({(t : G)} : Set G) ≤ L ⊓ M := by
  rw [← centralizer_intersection_of_projection ht]
  exact inf_le_inf_left L hCM

end CFSG.Quasithin.Chapter2.ComponentRefinement

end
