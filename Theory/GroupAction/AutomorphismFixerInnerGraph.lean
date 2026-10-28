module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

open Subgroup
/-!
# Automorphism fixers with two inner-automorphism cosets

When a subgroup has trivial ambient centralizer, its pointwise automorphism
fixer injects into the outer automorphism quotient. If all automorphisms are
inner or a fixed automorphism times inner, that quotient has at most two
elements. The fixer therefore also has order at most two.

The argument is purely group theoretic and applies without finiteness.
It supplies the final automorphism step for Aschbacher–Smith, 16.3.5,
printed p.1179, for the binary linear models.
-/

namespace MulAut
variable {K : Type*} [Group K]

/-- A subgroup with trivial ambient centralizer has pointwise automorphism
fixer of order at most two under inner/graph coverage. -/
public theorem fixing_card_le_two_of_inner_graph (P : Subgroup K)
    (hc : centralizer (P : Set K) = ⊥) (τ : MulAut K)
    (hcover : ∀ a : MulAut K, ∃ g : K, a = conj g ∨ a = τ * conj g) :
    Nat.card (fixingSubgroup (MulAut K) (P : Set K)) ≤ 2 := by
  classical
  let q := QuotientGroup.mk' (innerSubgroup K)
  have hi (g : K) : q (conj g) = 1 := by
    change QuotientGroup.mk (conj g) = 1
    rw [QuotientGroup.eq_one_iff]
    exact ⟨g, rfl⟩
  have htwo (x : Outer K) : x = 1 ∨ x = q τ := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (innerSubgroup K) x
    obtain ⟨g, rfl | rfl⟩ := hcover a
    · exact Or.inl (hi g)
    · exact Or.inr (by rw [map_mul, hi, mul_one])
  let b : Outer K → Bool := fun x => decide (x ≠ 1)
  have hb : Function.Injective b := by
    intro x y h
    by_cases hx : x = 1 <;> by_cases hy : y = 1
    · exact hx.trans hy.symm
    · simp [b, hx, hy] at h
    · simp [b, hx, hy] at h
    · exact ((htwo x).resolve_left hx).trans ((htwo y).resolve_left hy).symm
  let F := fixingSubgroup (MulAut K) (P : Set K)
  let f := q.comp F.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro a ha
    have hqa : q a.val = 1 := MonoidHom.mem_ker.mp ha
    change QuotientGroup.mk a.val = 1 at hqa
    rw [QuotientGroup.eq_one_iff] at hqa
    obtain ⟨g, hg⟩ := hqa
    have hgc : g ∈ centralizer (P : Set K) := by
      apply mem_centralizer_iff.mpr
      intro x hx
      have hfix : a.val x = x := a.property ⟨x, hx⟩
      rw [← hg] at hfix
      exact (mul_inv_eq_iff_eq_mul.mp hfix).symm
    have hg1 : g = 1 := mem_bot.mp (hc ▸ hgc)
    have ha1 : a.val = 1 := by rw [← hg, hg1, map_one]
    exact mem_bot.mpr (Subtype.ext ha1)
  have hh := Nat.card_le_card_of_injective (b ∘ f) (hb.comp hf)
  simpa using hh
end MulAut
