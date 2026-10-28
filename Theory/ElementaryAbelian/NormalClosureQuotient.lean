module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Elementary abelian quotients of normal closures

An abelian quotient of the normal closure of an elementary abelian p-subgroup
has exponent p: its generating conjugates already do, and powers distribute
over products in the quotient. The denominator need not be the whole center.
This supplies the literal orbit quotient in MS93 (3.6), printed p.871.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G]

theorem normalClosure_quotient_elementary (p : ℕ) (Y : Subgroup G)
    [IsElementaryAbelian p Y]
    (N : Subgroup (normalClosure (Y : Set G))) [N.Normal]
    (hab : IsMulCommutative ((normalClosure (Y : Set G)) ⧸ N)) :
    IsElementaryAbelian p ((normalClosure (Y : Set G)) ⧸ N) := by
  let A := normalClosure (Y : Set G)
  let q := QuotientGroup.mk' N
  let := hab
  have hp (x : G) (hx : x ∈ A) : q ⟨x,hx⟩ ^ p = 1 := by
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨y,hy,hyx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      have hxpow : x ^ p = 1 := by
        have hypow := elemPow_eq_one_of_isElementaryAbelian (p := p) y hy
        simpa only [hypow,isConj_one_right] using hyx.pow p
      have he : (⟨x,conjugatesOfSet_subset_normalClosure hx⟩ : A) ^ p = 1 :=
        Subtype.ext hxpow
      rw [←map_pow,he,map_one]
    | one => change q 1 ^ p = 1; rw [map_one,one_pow]
    | mul x y hx hy ihx ihy =>
      change (q ⟨x,hx⟩ * q ⟨y,hy⟩) ^ p = 1
      rw [mul_pow,ihx,ihy,one_mul]
    | inv x hx ih =>
      change (q ⟨x,hx⟩)⁻¹ ^ p = 1
      rw [inv_pow,ih,inv_one]
  refine {
    toIsMulCommutative := hab
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  induction x using QuotientGroup.induction_on with
  | H x => exact hp x x.property

end Subgroup
