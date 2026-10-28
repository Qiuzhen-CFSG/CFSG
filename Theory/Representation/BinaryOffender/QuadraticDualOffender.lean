module
public import Theory.Representation.BinaryOffender.Defs
public import Theory.Representation.QuadraticDuality
public import Mathlib.Algebra.Module.ZMod

/-!
# Quadratic actors with a bounded moved space are dual offenders

Faithful quadratic action in characteristic two forces every actor to
square to one, hence makes the actor elementary abelian. Duality identifies
the dual fixed codimension with the original moved-space dimension, so
the stated bound constructs an actual offender on the dual.
Source: Aschbacher–Smith, D.1.4, printed p.176.
-/

public section
namespace Representation.BinaryOffender
open Subgroup
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
theorem elementary_of_faithful_quadratic (ρ : Representation (ZMod 2) H W)
    (hρ : Function.Injective ρ) (A : Subgroup H) (hq : IsQuadratic ρ A) :
    IsElementaryAbelian 2 A := by
  have hp (a : A) : a ^ 2 = 1 := by
    apply Subtype.ext
    apply hρ
    apply LinearMap.ext
    intro w
    change ρ ((a : H)^2) w = ρ 1 w
    rw [pow_two, map_mul, Module.End.mul_apply, map_one, Module.End.one_apply]
    have he := hq a a.property a a.property w
    rw [map_sub, sub_eq_add_neg, sub_eq_add_neg, ZModModule.neg_eq_self,
      ZModModule.neg_eq_self, add_comm (ρ a w) w] at he
    exact add_right_cancel he
  exact
    { toIsMulCommutative :=
        ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
          (fun x => orderOf_dvd_of_pow_eq_one (hp x)) a b).eq⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp }

theorem dual_offender_of_quadratic_moved_bound (ρ : Representation (ZMod 2) H W)
    (hρ : Function.Injective ρ) (A : Subgroup H) (hne : A ≠ ⊥)
    (hq : IsQuadratic ρ A)
    (hdim : Module.finrank (ZMod 2) (Coinvariants.ker (ρ.comp A.subtype)) ≤ rank A) :
    IsOffender ρ.dual A := by
  refine ⟨⟨hne, elementary_of_faithful_quadratic ρ hρ A hq⟩, ?_⟩
  exact (Representation.finrank_dual_quotient_invariants (ρ.comp A.subtype)).le.trans hdim
end Representation.BinaryOffender

