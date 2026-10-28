module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Two anisotropic factors in a special group of order 64

This data describes two subgroups of order sixteen meeting in the elementary
center of order four and generating the whole group. Each factor has a
constant nonidentity square outside the center, and the two constants are
distinct. The centralizer of the first factor is exactly the center.

The data does not recognize a group: different multiplication laws satisfy
these conditions. Further control of the action on the center is needed.
The intended application is the product of involution centralizers in two
minus-extraspecial cores, as in Aschbacher, *Sporadic Groups* (1994), 8.15
and 46.2–46.3, printed pp.29–30 and 251.
-/

@[expose] public section

namespace Theory.GroupTheory
open Subgroup

variable (K : Type*) [Group K]

/-- Intrinsic factor geometry, without an isomorphism or an assumed action. -/
structure AnisotropicFactors where
  card : Nat.card K = 64
  center_card : Nat.card (center K) = 4
  center_elementary : IsElementaryAbelian 2 (center K)
  square_central : ∀ x : K, x ^ 2 ∈ center K
  A : Subgroup K
  B : Subgroup K
  A_card : Nat.card A = 16
  B_card : Nat.card B = 16
  inf_eq : A ⊓ B = center K
  sup_eq : A ⊔ B = ⊤
  z : center K
  u : center K
  z_ne_one : z ≠ 1
  u_ne_one : u ≠ 1
  distinct : z ≠ u
  A_square : ∀ x ∈ A, x ∉ center K → x ^ 2 = (z : K)
  B_square : ∀ x ∈ B, x ∉ center K → x ^ 2 = (u : K)
  centralizer_A : centralizer (A : Set K) = center K

variable {K} {J : Type*} [Group J]

/-- An isomorphism transports the literal fibers of the square map. -/
def squareFiberEquiv (e : K ≃* J) (c : K) :
    {x : K // x ^ 2 = c} ≃ {y : J // y ^ 2 = e c} where
  toFun x := ⟨e x, by rw [← map_pow, x.property]⟩
  invFun y := ⟨e.symm y, by
    apply e.injective
    simpa only [map_pow, e.apply_symm_apply] using y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)

theorem squareFiber_card_eq (e : K ≃* J) (c : K) :
    Nat.card {x : K // x ^ 2 = c} = Nat.card {y : J // y ^ 2 = e c} :=
  Nat.card_congr (squareFiberEquiv e c)

/-- A transitive automorphism action on the nonidentity center balances the
three nontrivial fibers of the square map. -/
theorem squareFiber_card_eq_of_center_transitive
    (h : ∀ c d : center K, c ≠ 1 → d ≠ 1 →
      ∃ a : MulAut K, a (c : K) = (d : K))
    (c d : center K) (hc : c ≠ 1) (hd : d ≠ 1) :
    Nat.card {x : K // x ^ 2 = (c : K)} =
      Nat.card {x : K // x ^ 2 = (d : K)} := by
  obtain ⟨a, ha⟩ := h c d hc hd
  simpa only [ha] using squareFiber_card_eq a (c : K)

end Theory.GroupTheory
