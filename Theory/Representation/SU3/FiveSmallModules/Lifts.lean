module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Prime-order images in a central quotient

In a faithful irreducible representation, a nonidentity central element
has no nonzero fixed vector. If the image of x modulo the center has prime
order p, then either x itself has order p or its nonidentity central power
x^p forces its entire fixed space to vanish. This treats arbitrary lifts
without identifying the central cover or bounding its center.

The application is the order-seven calculation for the small PSU₃(5)
modules in Guralnick–Malle, *Classification of 2F-modules I*, Proposition
4.3, manuscript pp.10–11, used in Aschbacher–Smith K.2, printed p.453.
-/

public section
open Subgroup Representation

namespace Representation.SU3.FiveSmallModules

/-- A nonidentity central power of an actor kills all of its fixed vectors. -/
theorem invariants_eq_bot_of_nontrivial_central_power
    {F R U : Type*} [Field F] [Group R] [AddCommGroup U] [Module F U]
    (τ : Representation F R U) (hf : Function.Injective τ) (hi : τ.IsIrreducible)
    (x : R) (n : ℕ) (hc : x ^ n ∈ center R) (hn : x ^ n ≠ 1) :
    invariants (τ.comp (zpowers x).subtype) = ⊥ := by
  let K : Subrepresentation τ :=
    ⟨(τ (x ^ n) - 1).ker, by
      intro g v hv
      change τ (x ^ n) v - v = 0 at hv
      change τ (x ^ n) (τ g v) - τ g v = 0
      have hcomm : τ (x ^ n) (τ g v) = τ g (τ (x ^ n) v) := by
        change (τ (x ^ n) * τ g) v = (τ g * τ (x ^ n)) v
        rw [← map_mul, ← map_mul, (mem_center_iff.mp hc g).symm]
      rw [hcomm, sub_eq_zero.mp hv, sub_self]⟩
  have hK : K = ⊥ := by
    rcases hi.eq_bot_or_eq_top K with h | h
    · exact h
    · exfalso
      apply hn
      apply hf
      rw [map_one]
      ext v
      have hv : v ∈ K := by rw [h]; trivial
      exact sub_eq_zero.mp hv
  apply le_bot_iff.mp
  intro v hv
  have hvK : v ∈ K := by
    change τ (x ^ n) v - v = 0
    exact sub_eq_zero.mpr (hv ⟨x ^ n, pow_mem (mem_zpowers x) n⟩)
  rw [hK] at hvK
  exact hvK

/-- A prime-order projective actor either has that order already or fixes only zero. -/
theorem orderOf_eq_or_invariants_eq_bot_of_projective_prime_order
    {F R U : Type*} [Field F] [Group R] [AddCommGroup U] [Module F U]
    (τ : Representation F R U) (hf : Function.Injective τ) (hi : τ.IsIrreducible)
    (x : R) {p : ℕ} (hp : p.Prime)
    (hx : orderOf (QuotientGroup.mk' (center R) x) = p) :
    orderOf x = p ∨ invariants (τ.comp (zpowers x).subtype) = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hn : x ^ p = 1
  · left
    apply orderOf_eq_prime hn
    intro he
    have : p = 1 := by simpa only [he, map_one, orderOf_one] using hx.symm
    exact hp.ne_one this
  · right
    apply invariants_eq_bot_of_nontrivial_central_power τ hf hi x p _ hn
    apply (QuotientGroup.eq_one_iff (x ^ p)).mp
    change QuotientGroup.mk' (center R) (x ^ p) = 1
    rw [map_pow, ← hx, pow_orderOf_eq_one]

end Representation.SU3.FiveSmallModules
