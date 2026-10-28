module
public import Theory.Representation.BinaryAlternatingFiveFlag.Borel
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# The paired alternating-five Borel section

The point-stabilizer three-space has a fixed line and an irreducible
quotient of order four. Independent point stabilizers on two copies,
together with an exchange of the factors, act irreducibly on the quotient
by the product of those lines. A single three-cycle extracts a noncentral
vector supported in one factor; the existing one-factor theorem and the
exchange then generate both factors. Only sixteen vectors are used in the
new finite certificate.

Source: Aschbacher--Smith, 14.6.9(k), printed p.1027, with the binary
permutation conventions of B.3.
-/

@[expose] public section
namespace BinaryPermutation.AlternatingFiveFlag
open Subgroup FiveCentralizerGeometry AlternatingFiveBorel
abbrev V := Multiplicative Space
abbrev pairThree : Subgroup (V × V) := three.prod three
abbrev pairLine : Subgroup (V × V) := line.prod line

def act (g : B) (x : V) : V := Multiplicative.ofAdd (rho g.val.val x.toAdd)

theorem pairThree_card : Nat.card pairThree = 64 := by
  rw [Nat.card_congr (three.prodEquiv three).toEquiv, Nat.card_prod, three_card]

theorem pairLine_card : Nat.card pairLine = 4 := by
  rw [Nat.card_congr (line.prodEquiv line).toEquiv, Nat.card_prod, line_card]

private theorem cubic_difference_not_line (x : V) (hx : x ∈ three) (hxn : x ∉ line) :
    act c₀ x * x⁻¹ ∉ line := by
  have h : ∀ x : V, x ∈ three → x ∉ line → act c₀ x * x⁻¹ ∉ line := by decide +kernel
  exact h x hx hxn

private theorem first_factor_le
    (W : Subgroup (V × V)) (hline : pairLine ≤ W) (hthree : W ≤ pairThree)
    (hleft : ∀ g : B, ∀ x ∈ W, (act g x.1, x.2) ∈ W)
    (x : V × V) (hx : x ∈ W) (hxn : x.1 ∉ line) :
    three.prod (⊥ : Subgroup V) ≤ W := by
  let U := W.comap (MonoidHom.inl V V)
  have hl : line ≤ U := fun a ha => hline ⟨ha, line.one_mem⟩
  have ht : U ≤ three := fun a ha => (hthree ha).1
  have hi : ∀ g : B, ∀ a ∈ U, act g a ∈ U := by
    intro g a ha
    exact hleft g (a, 1) ha
  have hc : act c₀ x.1 * x.1⁻¹ ∈ U := by
    have hh := W.mul_mem (hleft c₀ x hx) (W.inv_mem hx)
    change (act c₀ x.1 * x.1⁻¹, x.2 * x.2⁻¹) ∈ W at hh
    change (act c₀ x.1 * x.1⁻¹, 1) ∈ W
    simpa only [mul_inv_cancel] using hh
  have hnc : act c₀ x.1 * x.1⁻¹ ∉ line :=
    cubic_difference_not_line x.1 (hthree hx).1 hxn
  have hU : U = three := by
    rcases three_line_irreducible U hl ht hi with he | he
    · exact False.elim (hnc (he ▸ hc))
    · exact he
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  have hb' : b = 1 := hb
  subst b
  change a ∈ U
  exact hU.symm ▸ ha

theorem pair_line_irreducible_of_factor_exchange
    (W : Subgroup (V × V)) (hline : pairLine ≤ W) (hthree : W ≤ pairThree)
    (hleft : ∀ g : B, ∀ x ∈ W, (act g x.1, x.2) ∈ W)
    (hright : ∀ g : B, ∀ x ∈ W, (x.1, act g x.2) ∈ W)
    (hexchange : three.prod (⊥ : Subgroup V) ≤ W ↔
      (⊥ : Subgroup V).prod three ≤ W) :
    W = pairLine ∨ W = pairThree := by
  by_cases hle : W ≤ pairLine
  · exact Or.inl (le_antisymm hle hline)
  right
  obtain ⟨x, hx, hxn⟩ := SetLike.not_le_iff_exists.mp hle
  have hfirst : three.prod (⊥ : Subgroup V) ≤ W := by
    by_cases hx1 : x.1 ∈ line
    · have hx2 : x.2 ∉ line := fun hh => hxn ⟨hx1, hh⟩
      let W' := W.comap (MulEquiv.prodComm : V × V ≃* V × V).toMonoidHom
      have hl : pairLine ≤ W' := fun a ha => hline ⟨ha.2, ha.1⟩
      have ht : W' ≤ pairThree := fun a ha => ⟨(hthree ha).2, (hthree ha).1⟩
      have hi : ∀ g : B, ∀ a ∈ W', (act g a.1, a.2) ∈ W' := by
        intro g a ha
        exact hright g (a.2, a.1) ha
      have hf := first_factor_le W' hl ht hi (x.2, x.1) hx hx2
      apply hexchange.mpr
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      exact hf (show (b, a) ∈ three.prod (⊥ : Subgroup V) from ⟨hb, ha⟩)
    · exact first_factor_le W hline hthree hleft x hx hx1
  have hsecond := hexchange.mp hfirst
  apply le_antisymm hthree
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  have hmul := W.mul_mem (hfirst (show (a, 1) ∈ three.prod (⊥ : Subgroup V) from
    ⟨ha, (⊥ : Subgroup V).one_mem⟩))
    (hsecond (show (1, b) ∈ (⊥ : Subgroup V).prod three from ⟨(⊥ : Subgroup V).one_mem, hb⟩))
  simpa only [Prod.mk_mul_mk, mul_one, one_mul] using hmul

theorem pair_line_irreducible
    (W : Subgroup (V × V)) (hline : pairLine ≤ W) (hthree : W ≤ pairThree)
    (hleft : ∀ g : B, ∀ x ∈ W, (act g x.1, x.2) ∈ W)
    (hswap : ∀ x ∈ W, (x.2, x.1) ∈ W) :
    W = pairLine ∨ W = pairThree := by
  apply pair_line_irreducible_of_factor_exchange W hline hthree hleft
  · intro g x hx
    exact hswap _ (hleft g _ (hswap x hx))
  · constructor
    · intro h x hx
      exact hswap (x.2, x.1) (h (show (x.2, x.1) ∈ three.prod (⊥ : Subgroup V) from
        ⟨hx.2, hx.1⟩))
    · intro h x hx
      exact hswap (x.2, x.1) (h (show (x.2, x.1) ∈ (⊥ : Subgroup V).prod three from
        ⟨hx.2, hx.1⟩))

end BinaryPermutation.AlternatingFiveFlag
