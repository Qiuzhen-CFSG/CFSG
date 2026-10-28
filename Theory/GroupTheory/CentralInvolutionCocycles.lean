module
public import Theory.GroupTheory.ElementaryQuotientCocycles
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Cocycle correction through the center

For an involution automorphism, trivial cocycles on the elementary center
and elementary central quotient imply trivial cocycles on the group. The
fixed subgroup order criteria are retained on both actual induced actions.
Source: Aschbacher, *Sporadic Groups*, Exercise 2.8 and45.5(4).
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {R : Type*} [Group R]
@[expose] noncomputable def centerQuotientAction (α : MulAut R) : MulAut (R ⧸ center R) :=
  QuotientGroup.congr (center R) (center R) α
    ((characteristic_iff_map_eq.mp inferInstance) α)

theorem centerQuotientAction_apply (α : MulAut R) (r : R) :
    centerQuotientAction α (QuotientGroup.mk' (center R) r) =
      QuotientGroup.mk' (center R) (α r) := rfl

theorem central_involution_cocycle [Finite R]
    [IsElementaryAbelian 2 (center R)] [IsElementaryAbelian 2 (R ⧸ center R)]
    (α : MulAut R) (hα : ∀ r, α (α r) = r)
    (hc : Nat.card ((centerCongr α).toMonoidHom.eqLocus
      (MonoidHom.id (center R))) ^ 2 = Nat.card (center R))
    (hq : Nat.card ((centerQuotientAction α).toMonoidHom.eqLocus
      (MonoidHom.id (R ⧸ center R))) ^ 2 = Nat.card (R ⧸ center R))
    (x : R) (hx : x * α x = 1) : ∃ y : R, x = y * α y⁻¹ := by
  let f := QuotientGroup.mk' (center R)
  have hβ (a : R ⧸ center R) : centerQuotientAction α (centerQuotientAction α a) = a := by
    obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective (center R) a
    rw [centerQuotientAction_apply, centerQuotientAction_apply, hα]
  refine cocycle_of_elementary_quotient f (QuotientGroup.mk'_surjective _)
    α.toMonoidHom hα (centerQuotientAction α).toMonoidHom hβ
    (fun _ => rfl) hq ?_ x hx
  intro v hv hvα
  have hvZ : v ∈ center R := (QuotientGroup.eq_one_iff _).mp hv
  let vZ : center R := ⟨v, hvZ⟩
  have hαZ (a : center R) : centerCongr α (centerCongr α a) = a :=
    Subtype.ext (hα a)
  have hvfix : centerCongr α vZ = vZ := by
    apply Subtype.ext
    change α v = v
    have hv2 : v*v=1 := by
      have hh : vZ ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (center R)) vZ
      have hh' : v^2=1 := congrArg (fun w : center R => (w:R)) hh
      simpa only [pow_two] using hh'
    exact mul_left_cancel (hvα.trans hv2.symm)
  obtain ⟨y,hy⟩ := elementary_fixed_is_coboundary (centerCongr α).toMonoidHom
    hαZ hc vZ hvfix
  exact ⟨y,congrArg Subtype.val hy⟩
end Theory.GroupTheory
