module
public import Theory.Representation.BinaryAlternatingFiveFlag.Borel
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Paired regular four-groups under point-stabilizer conjugation

Independent alternating-four point stabilizers on two regular four-groups,
together with an exchange of the two supported factors, act irreducibly on
their product. A fixed three-cycle has no nonidentity fixed point on a
four-group. Its conjugation difference extracts an element supported in one
factor, whose orbit generates that factor; exchange then gives the other.
The only finite certificates inspect the four explicitly listed elements.

This is the quotient geometry used for the section Rz/A in the original
Aschbacher--Smith 14.6.9(l), printed p.1027. The acting group need only
exchange the supported factors; no larger Sylow normalizer is presumed.
-/

@[expose] public section
namespace BinaryPermutation.AlternatingFiveFlag
open Subgroup AlternatingFiveBorel

/-- The actual point-stabilizer conjugation on its regular four-group. -/
def fourConj (g : B) (x : four) : four :=
  ⟨g.val.val * x.val * g.val.val⁻¹,
    (normalizes_four_of_fixes g.val.val g.property x.val).mp x.property⟩

@[simp] theorem fourConj_val (g : B) (x : four) :
    (fourConj g x).val = g.val.val * x.val * g.val.val⁻¹ := rfl

private theorem cubic_four_orbit : ∀ x y : four, x ≠ 1 →
    y = 1 ∨ y = x ∨ y = fourConj c₀ x ∨ y = fourConj (c₀ * c₀) x := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  rcases hx with rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl <;> decide +kernel

private theorem cubic_four_difference : ∀ x : four, x ≠ 1 →
    fourConj c₀ x * x⁻¹ ≠ 1 := by
  rintro ⟨x, hx⟩
  rcases hx with rfl | rfl | rfl | rfl <;> decide +kernel

/-- Conjugation by the point stabilizer is irreducible on its regular four-group. -/
theorem four_irreducible (U : Subgroup four)
    (hi : ∀ g : B, ∀ x ∈ U, fourConj g x ∈ U) : U = ⊥ ∨ U = ⊤ := by
  by_cases hle : U ≤ ⊥
  · exact Or.inl (le_bot_iff.mp hle)
  right
  obtain ⟨x, hx, hxn⟩ := SetLike.not_le_iff_exists.mp hle
  apply eq_top_iff.mpr
  intro y _
  rcases cubic_four_orbit x y hxn with rfl | rfl | rfl | rfl
  · exact U.one_mem
  · exact hx
  · exact hi c₀ x hx
  · exact hi (c₀ * c₀) x hx

private theorem first_four_factor_le
    (W : Subgroup (four × four))
    (hleft : ∀ g : B, ∀ x ∈ W, (fourConj g x.1, x.2) ∈ W)
    (x : four × four) (hx : x ∈ W) (hxn : x.1 ≠ 1) :
    (⊤ : Subgroup four).prod (⊥ : Subgroup four) ≤ W := by
  let U := W.comap (MonoidHom.inl four four)
  have hi : ∀ g : B, ∀ a ∈ U, fourConj g a ∈ U := by
    intro g a ha
    exact hleft g (a, 1) ha
  have hc : fourConj c₀ x.1 * x.1⁻¹ ∈ U := by
    have hh := W.mul_mem (hleft c₀ x hx) (W.inv_mem hx)
    change (fourConj c₀ x.1 * x.1⁻¹, x.2 * x.2⁻¹) ∈ W at hh
    change (fourConj c₀ x.1 * x.1⁻¹, 1) ∈ W
    simpa only [mul_inv_cancel] using hh
  have hnc := cubic_four_difference x.1 hxn
  have hU : U = ⊤ := by
    rcases four_irreducible U hi with he | he
    · rw [he] at hc
      exact False.elim (hnc hc)
    · exact he
  rintro ⟨a, b⟩ ⟨_, hb⟩
  have hb' : b = 1 := hb
  subst b
  change a ∈ U
  rw [hU]
  trivial

/-- Independent point stabilizers and a factor exchange act irreducibly on V₄ × V₄. -/
theorem pair_four_irreducible_of_factor_exchange
    (W : Subgroup (four × four))
    (hleft : ∀ g : B, ∀ x ∈ W, (fourConj g x.1, x.2) ∈ W)
    (hright : ∀ g : B, ∀ x ∈ W, (x.1, fourConj g x.2) ∈ W)
    (hexchange : (⊤ : Subgroup four).prod (⊥ : Subgroup four) ≤ W ↔
      (⊥ : Subgroup four).prod (⊤ : Subgroup four) ≤ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hle : W ≤ ⊥
  · exact Or.inl (le_bot_iff.mp hle)
  right
  obtain ⟨x, hx, hxn⟩ := SetLike.not_le_iff_exists.mp hle
  have hfirst : (⊤ : Subgroup four).prod (⊥ : Subgroup four) ≤ W := by
    by_cases hx1 : x.1 = 1
    · have hx2 : x.2 ≠ 1 := fun hh => hxn (Prod.ext hx1 hh)
      let W' := W.comap (MulEquiv.prodComm : four × four ≃* four × four).toMonoidHom
      have hi : ∀ g : B, ∀ a ∈ W', (fourConj g a.1, a.2) ∈ W' := by
        intro g a ha
        exact hright g (a.2, a.1) ha
      have hf := first_four_factor_le W' hi (x.2, x.1) hx hx2
      apply hexchange.mpr
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      exact hf (show (b, a) ∈ (⊤ : Subgroup four).prod (⊥ : Subgroup four) from ⟨hb, ha⟩)
    · exact first_four_factor_le W hleft x hx hx1
  have hsecond := hexchange.mp hfirst
  apply eq_top_iff.mpr
  rintro ⟨a, b⟩ _
  have hmul := W.mul_mem (hfirst (show (a, 1) ∈ (⊤ : Subgroup four).prod (⊥ : Subgroup four) from
    ⟨mem_top a, (⊥ : Subgroup four).one_mem⟩))
    (hsecond (show (1, b) ∈ (⊥ : Subgroup four).prod (⊤ : Subgroup four) from
      ⟨(⊥ : Subgroup four).one_mem, mem_top b⟩))
  simpa only [Prod.mk_mul_mk, mul_one, one_mul] using hmul

/-- A literal coordinate swap is sufficient for the exchange hypothesis. -/
theorem pair_four_irreducible
    (W : Subgroup (four × four))
    (hleft : ∀ g : B, ∀ x ∈ W, (fourConj g x.1, x.2) ∈ W)
    (hswap : ∀ x ∈ W, (x.2, x.1) ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  apply pair_four_irreducible_of_factor_exchange W hleft
  · intro g x hx
    exact hswap _ (hleft g _ (hswap x hx))
  · constructor
    · intro h x hx
      exact hswap (x.2, x.1) (h (show (x.2, x.1) ∈
        (⊤ : Subgroup four).prod (⊥ : Subgroup four) from ⟨hx.2, hx.1⟩))
    · intro h x hx
      exact hswap (x.2, x.1) (h (show (x.2, x.1) ∈
        (⊥ : Subgroup four).prod (⊤ : Subgroup four) from ⟨hx.2, hx.1⟩))

end BinaryPermutation.AlternatingFiveFlag
