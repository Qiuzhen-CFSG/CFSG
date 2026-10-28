module

public import Theory.GroupTheory.QuaternionCentralProductIntrinsic
public import Theory.ElementaryAbelian.ExtraspecialSuitableLift

/-!
# The intrinsic outer action of a quaternion central product

For a central product of two quaternion eights, the action of automorphisms on
the quotient by the actual center has precisely the inner automorphisms as its
kernel. The square map on that quotient is already constructed in
`QuaternionCentralProductIntrinsic`.

The kernel calculation uses extraspecial commutator duality: a central
displacement functional is represented by conjugation. This applies to the
literal factor-generated group, with no abstract replacement.

Source: Aschbacher--Smith, Lemma 14.2.21, printed p.988, PDF p.1005.
-/

namespace Subgroup.QuaternionCentralProductData

open scoped commutatorElement

variable {Q : Type*} [Group Q] [Finite Q] (d : Subgroup.QuaternionCentralProductData Q)

include d

/-- An automorphism invisible on the central quotient is inner. -/
public theorem quotientAut_eq_one_iff_inner (a : MulAut Q) :
    Subgroup.quotientAut (Subgroup.center Q) a = 1 ↔
      a ∈ (MulAut.conj : Q →* MulAut Q).range := by
  let _ : IsExtraspecial 2 Q := d.extraspecial
  constructor
  · intro ha
    have hdisplacement (x : Q) : a x * x⁻¹ ∈ Subgroup.center Q := by
      have hx := DFunLike.congr_fun ha (QuotientGroup.mk' (Subgroup.center Q) x)
      rw [Subgroup.quotientAut_apply_mk] at hx
      have h := QuotientGroup.eq.mp hx.symm
      have hc := Normal.conj_mem (show (Subgroup.center Q).Normal from inferInstance)
        (x⁻¹ * a x) h x
      simpa only [mul_assoc, mul_inv_cancel_left] using hc
    obtain ⟨r, hr⟩ := extraspecial_two_exists_inner_twist_fixing_subgroup
      (⊤ : Subgroup Q) le_top a
      (fun z hz => d.fixes_center a ⟨z, hz⟩)
      (fun x _ => hdisplacement x)
    have heq : a * MulAut.conj r = 1 := by
      apply MulEquiv.ext
      intro x
      exact hr x (Subgroup.mem_top x)
    refine ⟨r⁻¹, ?_⟩
    have h := mul_eq_one_iff_eq_inv.mp heq
    simpa only [map_inv] using h.symm
  · rintro ⟨r, rfl⟩
    apply MulEquiv.ext
    intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Q) v
    rw [Subgroup.quotientAut_apply_mk]
    have hc : ⁅r, x⁆ ∈ Subgroup.center Q := by
      let _ := d.quotient_elementary
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' (Subgroup.center Q)) ⁅r, x⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        ((d.quotient_elementary.toIsMulCommutative).is_comm.comm _ _)
    change QuotientGroup.mk' (Subgroup.center Q) ((MulAut.conj r) x) =
      QuotientGroup.mk' (Subgroup.center Q) x
    have hq : QuotientGroup.mk' (Subgroup.center Q) ⁅r, x⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hc
    rw [conj_eq_commutatorElement_mul, map_mul, hq, one_mul]

/-- The kernel of the literal central-quotient action is the inner group. -/
public theorem quotientAut_ker_eq_inner :
    (Subgroup.quotientAut (Subgroup.center Q)).ker =
      (MulAut.conj : Q →* MulAut Q).range := by
  ext a
  exact d.quotientAut_eq_one_iff_inner a

end Subgroup.QuaternionCentralProductData
