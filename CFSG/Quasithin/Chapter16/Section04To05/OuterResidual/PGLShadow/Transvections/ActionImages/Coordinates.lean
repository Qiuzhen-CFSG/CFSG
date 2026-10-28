module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.Transvections.ActionImages.BinaryModel

/-!
# Marked coordinates on an elementary eight

Evaluation of the three binary coordinates at the three marked generators is
surjective by generation and bijective by the order-eight hypothesis. Agreement
on those generators then identifies the three actual transvections with the
explicit binary maps. This is the coordinate transport for the action argument
in Aschbacher–Smith, Lemma 16.4.6, printed pp.1185–1186.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.Transvections
namespace ActionCoordinates
open ActionModel (C E)

private def bitHom {H : Type*} [Group H] (g : H) (hg : g ^ 2 = 1) : C →* H where
  toFun x := g ^ x.toAdd.val
  map_one' := by simp
  map_mul' x y := by
    change g ^ (x.toAdd + y.toAdd).val = g ^ x.toAdd.val * g ^ y.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod (x.toAdd.val + y.toAdd.val) hg).symm

variable {H : Type*} [Group H] [IsElementaryAbelian 2 H]

private def eval (r z v : H) : E →* H :=
  (bitHom r (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 H) r)).coprod
  ((bitHom z (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 H) z)).coprod
  (bitHom v (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 H) v)))

private theorem eval_r (r z v : H) : eval r z v ActionModel.r = r := by
  simp [eval, bitHom, ActionModel.r, show (1 : ZMod 2).val = 1 by decide]
private theorem eval_z (r z v : H) : eval r z v ActionModel.z = z := by
  simp [eval, bitHom, ActionModel.z, show (1 : ZMod 2).val = 1 by decide]
private theorem eval_v (r z v : H) : eval r z v ActionModel.v = v := by
  simp [eval, bitHom, ActionModel.v, show (1 : ZMod 2).val = 1 by decide]

noncomputable def coordinates (r z v : H) (hc : Nat.card H = 8)
    (hg : zpowers r ⊔ (zpowers z ⊔ zpowers v) = ⊤) : E ≃* H := by
  have hs : Function.Surjective (eval r z v) := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← hg]
    exact sup_le (zpowers_le.mpr ⟨ActionModel.r, eval_r r z v⟩)
      (sup_le (zpowers_le.mpr ⟨ActionModel.z, eval_z r z v⟩)
        (zpowers_le.mpr ⟨ActionModel.v, eval_v r z v⟩))
  have hm : Nat.card E = 8 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  exact MulEquiv.ofBijective (eval r z v) (hs.bijective_of_nat_card_le (by rw [hc, hm]))

theorem coordinates_r (r z v : H) (hc hg) : coordinates r z v hc hg ActionModel.r = r :=
  eval_r r z v
theorem coordinates_z (r z v : H) (hc hg) : coordinates r z v hc hg ActionModel.z = z :=
  eval_z r z v
theorem coordinates_v (r z v : H) (hc hg) : coordinates r z v hc hg ActionModel.v = v :=
  eval_v r z v

omit [IsElementaryAbelian 2 H] in
theorem hom_ext {f g : E →* H}
    (hr : f ActionModel.r = g ActionModel.r)
    (hz : f ActionModel.z = g ActionModel.z)
    (hv : f ActionModel.v = g ActionModel.v) : f = g := by
  have decomp : ∀ x : E, x = ActionModel.r ^ x.1.toAdd.val *
      (ActionModel.z ^ x.2.1.toAdd.val * ActionModel.v ^ x.2.2.toAdd.val) := by
    decide +kernel
  apply MonoidHom.ext
  intro x
  rw [decomp x]
  simp only [map_mul, map_pow, hr, hz, hv]

omit [IsElementaryAbelian 2 H] in
theorem transport_s (e : E ≃* H) (S : MulAut H)
    (hr : S (e ActionModel.r) = e ActionModel.r)
    (hz : S (e ActionModel.z) = e (ActionModel.z * ActionModel.u))
    (hv : S (e ActionModel.v) = e (ActionModel.u * ActionModel.v)) :
    MulAut.congr e.symm S = ActionModel.s := by
  have h : S.toMonoidHom.comp e.toMonoidHom =
      e.toMonoidHom.comp ActionModel.s.toMonoidHom := by
    apply hom_ext
    · simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        show ActionModel.s ActionModel.r = ActionModel.r by decide +kernel] using hr
    · simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        show ActionModel.s ActionModel.z = ActionModel.z * ActionModel.u by decide +kernel] using hz
    · simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        show ActionModel.s ActionModel.v = ActionModel.u * ActionModel.v by decide +kernel] using hv
  apply MulEquiv.ext
  intro x
  apply e.injective
  change e (e.symm (S (e x))) = e (ActionModel.s x)
  rw [e.apply_symm_apply]
  exact DFunLike.congr_fun h x

omit [IsElementaryAbelian 2 H] in
theorem transport_t (e : E ≃* H) (T : MulAut H)
    (hr : T (e ActionModel.r) = e (ActionModel.r * ActionModel.v))
    (hz : T (e ActionModel.z) = e ActionModel.z)
    (hv : T (e ActionModel.v) = e ActionModel.v) :
    MulAut.congr e.symm T = ActionModel.t := by
  have h : T.toMonoidHom.comp e.toMonoidHom =
      e.toMonoidHom.comp ActionModel.t.toMonoidHom := by
    apply hom_ext
    · simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        show ActionModel.t ActionModel.r = ActionModel.r * ActionModel.v by decide +kernel] using hr
    · simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        show ActionModel.t ActionModel.z = ActionModel.z by decide +kernel] using hz
    · simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        show ActionModel.t ActionModel.v = ActionModel.v by decide +kernel] using hv
  apply MulEquiv.ext
  intro x
  apply e.injective
  change e (e.symm (T (e x))) = e (ActionModel.t x)
  rw [e.apply_symm_apply]
  exact DFunLike.congr_fun h x

omit [IsElementaryAbelian 2 H] in
theorem transport_a (e : E ≃* H) (A : MulAut H)
    (hr : A (e ActionModel.r) = e (ActionModel.r * ActionModel.z))
    (hz : A (e ActionModel.z) = e ActionModel.z)
    (hv : A (e ActionModel.v) = e ActionModel.v) :
    MulAut.congr e.symm A = ActionModel.a := by
  have h : A.toMonoidHom.comp e.toMonoidHom =
      e.toMonoidHom.comp ActionModel.a.toMonoidHom := by
    apply hom_ext
    · simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        show ActionModel.a ActionModel.r = ActionModel.r * ActionModel.z by decide +kernel] using hr
    · simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        show ActionModel.a ActionModel.z = ActionModel.z by decide +kernel] using hz
    · simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        show ActionModel.a ActionModel.v = ActionModel.v by decide +kernel] using hv
  apply MulEquiv.ext
  intro x
  apply e.injective
  change e (e.symm (A (e x))) = e (ActionModel.a x)
  rw [e.apply_symm_apply]
  exact DFunLike.congr_fun h x

end ActionCoordinates
end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.Transvections
