module

public import Theory.GroupTheory.SpecificGroups.PermThreeProduct
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Automorphisms of the two symmetric-three factors

An automorphism of S₃ × S₃ either exchanges the coordinate factors or is
inner. The normal-subgroup classification identifies the image of the first
factor. In the preserving case its centralizer identifies the second factor;
both restrictions are inner because two distinct transpositions determine
an automorphism of S₃. The finite checks involve only the six permutations.

This supplies the group-theoretic step in the binary determinant-action
normalizer used in Aschbacher–Smith, printed pp.1121–1122 and 1146–1147.
-/

public section
open Subgroup
namespace Theory.GroupTheory.PermThreeProduct
local notation "S" => Equiv.Perm (Fin 3)
private def s : S := Equiv.swap 0 1
private def t : S := Equiv.swap 1 2

private theorem pair_conjugate : ∀ a b : S,
    a * a = 1 → b * b = 1 → a ≠ 1 → b ≠ 1 → a ≠ b →
    ∃ c : S, c * s * c⁻¹ = a ∧ c * t * c⁻¹ = b := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide +kernel

private theorem six_words : ∀ x : S,
    x = 1 ∨ x = s ∨ x = t ∨ x = s * t ∨ x = t * s ∨ x = s * t * s := by
  decide +kernel

private theorem aut_inner (e : MulAut S) : ∃ c : S, ∀ x, e x = c * x * c⁻¹ := by
  obtain ⟨c, hs, ht⟩ := pair_conjugate (e s) (e t)
    (by simpa only [map_mul, map_one] using congrArg e (show s * s = 1 by decide))
    (by simpa only [map_mul, map_one] using congrArg e (show t * t = 1 by decide))
    (fun h => (show s ≠ 1 by decide) (e.injective (h.trans e.map_one.symm)))
    (fun h => (show t ≠ 1 by decide) (e.injective (h.trans e.map_one.symm)))
    (fun h => (show s ≠ t by decide) (e.injective h))
  refine ⟨c, fun x => ?_⟩
  rcases six_words x with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [map_one, map_mul, ← hs, ← ht] <;> group

private theorem center_trivial : ∀ x : S, (∀ y, y * x = x * y) → x = 1 := by
  decide +kernel

local notation "first" => Subgroup.prod (⊤ : Subgroup S) ⊥
local notation "second" => Subgroup.prod (⊥ : Subgroup S) ⊤

private theorem inl_range : (MonoidHom.inl S S).range = first := by
  ext x
  change (∃ a, (a, 1) = x) ↔ True ∧ x.2 = 1
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨trivial, rfl⟩
  · rintro ⟨_, h⟩; exact ⟨x.1, Prod.ext rfl h.symm⟩

/-- Every automorphism either is inner or takes the first factor onto the second. -/
theorem automorphism_inner_or_exchange (e : MulAut (S × S)) :
    (∃ c : S × S, ∀ x, e x = c * x * c⁻¹) ∨
      (e.toMonoidHom.comp (MonoidHom.inl S S)).range = second := by
  let f := e.toMonoidHom.comp (MonoidHom.inl S S)
  have hf : Function.Injective f := e.injective.comp (fun a b h => congrArg Prod.fst h)
  have hnormal : f.range.Normal := by
    dsimp only [f]
    rw [MonoidHom.range_comp, inl_range]
    exact (inferInstance : ((⊤ : Subgroup S).prod ⊥).Normal).map _ e.surjective
  rcases Theory.GroupTheory.PermThreeProduct.normal_subgroup_eq_factor
      f.range (MonoidHom.ofInjective hf).symm with hl | hr
  · left
    have hleft (a : S) : (e (a, 1)).2 = 1 := by
      have h : f a ∈ (⊤ : Subgroup S).prod ⊥ := by rw [← hl]; exact ⟨a, rfl⟩
      exact h.2
    have hright (b : S) : (e (1, b)).1 = 1 := by
      apply center_trivial
      intro y
      obtain ⟨a, ha⟩ := show (y, 1) ∈ f.range from hl.symm ▸ ⟨mem_top y, rfl⟩
      have h : e (a, 1) * e (1, b) = e (1, b) * e (a, 1) := by
        rw [← map_mul, ← map_mul]
        congr 1
      change e (a, 1) = (y, 1) at ha
      rw [ha] at h
      exact congrArg Prod.fst h
    let f₁ := (MonoidHom.fst S S).comp f
    let f₂ := (MonoidHom.snd S S).comp
      (e.toMonoidHom.comp (MonoidHom.inr S S))
    have hi₁ : Function.Injective f₁ := by
      intro a b h
      apply hf
      exact Prod.ext h ((hleft a).trans (hleft b).symm)
    have hi₂ : Function.Injective f₂ := by
      intro a b h
      have he : e (1, a) = e (1, b) :=
        Prod.ext ((hright a).trans (hright b).symm) h
      exact congrArg Prod.snd (e.injective he)
    obtain ⟨c, hc⟩ := aut_inner (MulEquiv.ofBijective f₁
      ⟨hi₁, Finite.surjective_of_injective hi₁⟩)
    obtain ⟨d, hd⟩ := aut_inner (MulEquiv.ofBijective f₂
      ⟨hi₂, Finite.surjective_of_injective hi₂⟩)
    refine ⟨(c, d), fun x => ?_⟩
    have he : x = (x.1, 1) * (1, x.2) := by simp
    rw [he, map_mul]
    apply Prod.ext
    · change (e (x.1, 1)).1 * (e (1, x.2)).1 = c * (x.1 * 1) * c⁻¹
      rw [hright, mul_one, mul_one]
      exact hc x.1
    · change (e (x.1, 1)).2 * (e (1, x.2)).2 = d * (1 * x.2) * d⁻¹
      rw [hleft, one_mul, one_mul]
      exact hd x.2
  · exact Or.inr hr

end Theory.GroupTheory.PermThreeProduct
