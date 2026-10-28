module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

/-!
# Fourth powers in derived subgroups of groups of class at most three

Suppose the third lower central subgroup is central and every element is a
product of two elements with central squares. Then the derived subgroup has
exponent dividing four. The three subgroups lemma first makes the derived
subgroup abelian. If a has central square, conjugation by a inverts [a, b];
centrality of the third commutator then makes [a, b]² central and [a, b]⁴ = 1.
The two-factor decomposition and closure of the derived subgroup finish.

This elementary commutator calculation is used for central extensions of
UT₃(F₄) in the two-primary bound for Aschbacher--Smith I.1.3(6), printed
p.407 (PDF p.418), whose multiplier reference is GLS3 §6.1. It assumes no
multiplier calculation and imposes no finiteness hypothesis.
-/

open scoped commutatorElement
namespace Subgroup

variable {G : Type*} [Group G]

private theorem derived_commute
    (hc : ⁅_root_.commutator G, (⊤ : Subgroup G)⁆ ≤ center G)
    {x y : G} (hx : x ∈ _root_.commutator G) (hy : y ∈ _root_.commutator G) :
    Commute x y := by
  have ht : ⁅center G, (⊤ : Subgroup G)⁆ = ⊥ :=
    commutator_center_left ⊤
  have h₁ : ⁅⁅_root_.commutator G, (⊤ : Subgroup G)⁆, (⊤ : Subgroup G)⁆ = ⊥ :=
    eq_bot_iff.mpr ((commutator_mono hc le_rfl).trans_eq ht)
  have h₂ : ⁅⁅(⊤ : Subgroup G), _root_.commutator G⁆, (⊤ : Subgroup G)⁆ = ⊥ := by
    rwa [commutator_comm (⊤ : Subgroup G)]
  have hd : ⁅_root_.commutator G, _root_.commutator G⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate h₂ h₁
  apply commutatorElement_eq_one_iff_commute.mp
  exact mem_bot.mp (hd ▸ commutator_mem_commutator hx hy)

private theorem generator_commutator_four
    (hc : ⁅_root_.commutator G, (⊤ : Subgroup G)⁆ ≤ center G)
    (a b : G) (ha : a ^ 2 ∈ center G) : ⁅a, b⁆ ^ 4 = 1 := by
  let c := ⁅a, b⁆
  have hsq : ⁅a * a, b⁆ = 1 := by
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    simpa only [pow_two] using (mem_center_iff.mp ha b).symm
  have hi : a * c * a⁻¹ = c⁻¹ := by
    have h : (a * c * a⁻¹) * c = 1 := by
      simpa only [commutatorElement_mul_left_eq_conj_mul] using hsq
    exact mul_eq_one_iff_eq_inv.mp h
  have hz : ⁅a, c⁆ ∈ center G := by
    have hmem := hc (commutator_mem_commutator
      (commutator_mem_commutator (mem_top a) (mem_top b)) (mem_top a))
    simpa only [commutatorElement_inv] using (center G).inv_mem hmem
  have hi2 : c⁻¹ * c⁻¹ ∈ center G := by
    simpa only [commutatorElement_def, hi] using hz
  have hc2 : c ^ 2 ∈ center G := by
    simpa only [mul_inv_rev, inv_inv, pow_two] using (center G).inv_mem hi2
  have he : (MulAut.conj a) (c ^ 2) = c ^ 2 := by
    change a * c ^ 2 * a⁻¹ = c ^ 2
    rw [mem_center_iff.mp hc2 a, mul_inv_cancel_right]
  have he' : c⁻¹ ^ 2 = c ^ 2 := by
    rw [map_pow] at he
    change (a * c * a⁻¹) ^ 2 = c ^ 2 at he
    rwa [hi] at he
  change c ^ 4 = 1
  calc
    c ^ 4 = c ^ 2 * c ^ 2 := by group
    _ = c ^ 2 * (c⁻¹) ^ 2 := by rw [← he']
    _ = 1 := by group

/-- Class three and factorizations into elements with central squares force
exponent four in the derived subgroup. -/
public theorem derived_pow_four_of_central_square_factors
    (hc : ⁅_root_.commutator G, (⊤ : Subgroup G)⁆ ≤ center G)
    (hf : ∀ x : G, ∃ a b : G, a ^ 2 ∈ center G ∧ b ^ 2 ∈ center G ∧ x = a * b)
    (x : G) (hx : x ∈ _root_.commutator G) : x ^ 4 = 1 := by
  rw [commutator_eq_closure] at hx
  refine Subgroup.closure_induction ?_ (by simp) ?_ ?_ hx
  · rintro x ⟨a, b, rfl⟩
    obtain ⟨u, v, hu, hv, rfl⟩ := hf a
    rw [commutatorElement_mul_left_eq_conj_mul]
    have h₁ : u * ⁅v, b⁆ * u⁻¹ ∈ _root_.commutator G :=
      (inferInstance : (_root_.commutator G).Normal).conj_mem _
        (commutator_mem_commutator (mem_top v) (mem_top b)) u
    have h₂ : ⁅u, b⁆ ∈ _root_.commutator G :=
      commutator_mem_commutator (mem_top u) (mem_top b)
    rw [(derived_commute hc h₁ h₂).mul_pow]
    have hconj : (u * ⁅v, b⁆ * u⁻¹) ^ 4 = 1 := by
      change ((MulAut.conj u) ⁅v, b⁆) ^ 4 = 1
      rw [← map_pow, generator_commutator_four hc v b hv, map_one]
    rw [hconj, generator_commutator_four hc u b hu, one_mul]
  · intro a b ha hb ha4 hb4
    have ha' : a ∈ _root_.commutator G := by rwa [commutator_eq_closure]
    have hb' : b ∈ _root_.commutator G := by rwa [commutator_eq_closure]
    rw [(derived_commute hc ha' hb').mul_pow, ha4, hb4, one_mul]
  · intro a _ ha
    rw [inv_pow, ha, inv_one]

end Subgroup
