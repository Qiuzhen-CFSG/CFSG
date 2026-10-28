module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure.Residual
public import Theory.Representation.PSL3Two.HomogeneousDouble.GroupSections
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Opposing sections of the actual pure-point central quotient

A normal subgroup with the full point-kernel image contains an embedded natural
four-space. Its center meets that space in precisely the marked line and acts
trivially on the whole four-space. Consequently its central quotient contains
the natural three-space and maps onto the dual three-space, for the same full
quotient actor. These opposing sections exclude a homogeneous irreducible double.

The hypotheses retain the original actor and the literal restriction of its
point action to the normal subgroup. No classification of an MS pair is used.
-/

@[expose] public noncomputable section
open Subgroup Representation BinaryLinear.OuterCyclic
open BinaryNaturalDual.VectorStabilizers.Pure
open Theory.LinearAlgebra.BinaryFivePointStabilizer
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.SourceDistanceFourSections

variable {D : Type*} [Group D] (Q : Subgroup D) [Q.Normal]

/-- Conjugation on the literal central quotient of the normal subgroup. -/
def centralAction : D →* MulAut (Q ⧸ center Q) :=
  (quotientAut (center Q)).comp (MulAut.conjNormal : D →* MulAut Q)

@[simp] theorem centralAction_mk (d : D) (q : Q) :
    centralAction Q d (QuotientGroup.mk' _ q) =
      QuotientGroup.mk' _ (MulAut.conjNormal d q) :=
  quotientAut_apply_mk _ _ _

private theorem mem_line_of_fixed {x v : Space 4} (hx : x ≠ 0)
    (hv : ∀ g : pointKernel x, g.val.val v = v) : v ∈ line x := by
  by_contra hn
  have hq : (line x).mkQ v ≠ 0 := fun he => hn ((Submodule.Quotient.mk_eq_zero _).mp he)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hq
  let w : line x := ⟨x, Submodule.mem_span_singleton_self x⟩
  have he := hv (kernelShear x (f.smulRight w))
  rw [kernelShear_apply] at he
  change v + f ((line x).mkQ v) • x = v at he
  rw [hf, one_smul] at he
  exact hx (add_left_cancel (he.trans (add_zero v).symm))

variable {x : Space 4}
  (f : D →* pointStabilizer x) (r : Q →* pointKernel x)
  (hr : ∀ q : Q, (r q).val = f q)
  (e : Multiplicative (Space 4) →* Q)
  (he : ∀ (d : D) (v : Space 4),
    MulAut.conjNormal d (e (Multiplicative.ofAdd v)) =
      e (Multiplicative.ofAdd ((f d).val v)))

include hr in
private theorem radical_conj (d : D) (q : Q) :
    (r (MulAut.conjNormal d q)).val = f d * (r q).val * (f d)⁻¹ := by
  rw [hr, hr]
  change f (d * (q : D) * d⁻¹) = _
  simp only [map_mul, map_inv]

include hr he in
private theorem natural_central_iff (hx : x ≠ 0) (hronto : Function.Surjective r)
    (hein : Function.Injective e) (v : Space 4) :
    e (Multiplicative.ofAdd v) ∈ center Q ↔ v ∈ line x := by
  constructor
  · intro hv
    apply mem_line_of_fixed hx
    intro g
    obtain ⟨q, rfl⟩ := hronto g
    have hc := (mem_center_iff.mp hv) q
    have hfix : MulAut.conjNormal (q : D) (e (Multiplicative.ofAdd v)) =
        e (Multiplicative.ofAdd v) := by
      rw [MulAut.conjNormal_val]
      change q * e (Multiplicative.ofAdd v) * q⁻¹ = e (Multiplicative.ofAdd v)
      rw [hc, mul_inv_cancel_right]
    rw [he] at hfix
    have hvf := congrArg Multiplicative.toAdd (hein hfix)
    rw [hr]
    exact hvf
  · intro hv
    apply mem_center_iff.mpr
    intro q
    have hh := he (q : D) v
    rw [fixes_line x (f q) v hv, MulAut.conjNormal_val] at hh
    change q * e (Multiplicative.ofAdd v) * q⁻¹ = e (Multiplicative.ofAdd v) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh

include hr he in
private theorem center_le_radical_ker (hein : Function.Injective e) :
    center Q ≤ r.ker := by
  intro z hz
  change r z = 1
  apply Subtype.ext
  rw [hr]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have hc := (mem_center_iff.mp hz) (e (Multiplicative.ofAdd v))
  have hfix : MulAut.conjNormal (z : D) (e (Multiplicative.ofAdd v)) =
      e (Multiplicative.ofAdd v) := by
    rw [MulAut.conjNormal_val]
    change z * e (Multiplicative.ofAdd v) * z⁻¹ = e (Multiplicative.ofAdd v)
    rw [← hc, mul_inv_cancel_right]
  rw [he] at hfix
  exact congrArg Multiplicative.toAdd (hein hfix)

private def displacementDual (hx : x ≠ 0) :
    (pointQuotient x →ₗ[ZMod 2] line x) ≃ₗ[ZMod 2]
      Module.Dual (ZMod 2) (pointQuotient x) :=
  LinearEquiv.congrRight (LinearEquiv.coord (ZMod 2) (Space 4) x hx)

private def dualProjection (hx : x ≠ 0) :
    Q →* Multiplicative (Module.Dual (ZMod 2) (pointQuotient x)) :=
  ((displacementDual hx).toAddEquiv.toMultiplicative.toMonoidHom.comp
    (kernelDisplacementEquiv x).toMonoidHom).comp r

include hr in
private theorem dualProjection_conj (hx : x ≠ 0) (d : D) (q : Q) :
    (dualProjection Q r hx (MulAut.conjNormal d q)).toAdd =
      (pointQuotientAction x (f d)).symm.dualMap (dualProjection Q r hx q).toAdd := by
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    have hqa : (pointQuotientAction x (f d)).symm ((line x).mkQ v) =
        (line x).mkQ ((f d).val.symm v) := by
      apply (pointQuotientAction x (f d)).injective
      rw [LinearEquiv.apply_symm_apply, quotientAction_mk, LinearEquiv.apply_symm_apply]
    change _ = (dualProjection Q r hx q).toAdd
      ((pointQuotientAction x (f d)).symm ((line x).mkQ v))
    rw [hqa]
    change LinearEquiv.coord (ZMod 2) (Space 4) x hx
        ((kernelDisplacementEquiv x (r (MulAut.conjNormal d q))).toAdd ((line x).mkQ v)) =
      LinearEquiv.coord (ZMod 2) (Space 4) x hx
        ((kernelDisplacementEquiv x (r q)).toAdd ((line x).mkQ ((f d).val.symm v)))
    rw [kernelDisplacementEquiv_apply, kernelDisplacementEquiv_apply]
    simp only [toAdd_ofAdd]
    apply congrArg (LinearEquiv.coord (ZMod 2) (Space 4) x hx)
    apply Subtype.ext
    rw [kernelDisplacement_mk, kernelDisplacement_mk]
    have hev := congrArg (fun a : pointStabilizer x => a.val v) (radical_conj Q f r hr d q)
    change (r (MulAut.conjNormal d q)).val.val v =
      (f d).val ((r q).val.val ((f d).val.symm v)) at hev
    rw [hev]
    have hf := fixes_line x (f d)
      ((r q).val.val ((f d).val.symm v) - (f d).val.symm v)
      ((mem_kernel_iff x (r q).val).mp (r q).property _)
    rw [map_sub, LinearEquiv.apply_symm_apply] at hf
    exact hf

include hr he in
/-- The literal point action and full radical image exclude a homogeneous
irreducible double on the central quotient of the original normal subgroup. -/
theorem not_homogeneous_double (hx : x ≠ 0) (hf : Function.Surjective f)
    (hronto : Function.Surjective r) (hein : Function.Injective e)
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    (σ : Representation (ZMod 2) D X) [IsIrreducible σ]
    (E : (Q ⧸ center Q) ≃* Multiplicative (X × X))
    (hE : ∀ d c, (E (centralAction Q d c)).toAdd =
      (σ d (E c).toAdd.1, σ d (E c).toAdd.2)) : False := by
  let π : Multiplicative (Space 4) →* Multiplicative (pointQuotient x) :=
    (line x).mkQ.toAddMonoidHom.toMultiplicative
  have hπ : Function.Surjective π := by
    intro v
    obtain ⟨w, hw⟩ := (line x).mkQ_surjective v.toAdd
    exact ⟨Multiplicative.ofAdd w, congrArg Multiplicative.ofAdd hw⟩
  let j : Multiplicative (Space 4) →* (Q ⧸ center Q) := (QuotientGroup.mk' _).comp e
  have hj : j.ker = π.ker := by
    ext v
    change (QuotientGroup.mk' _ (e v) = 1) ↔ π v = 1
    change ((e v : Q) : Q ⧸ center Q) = 1 ↔ π v = 1
    rw [QuotientGroup.eq_one_iff]
    change e (Multiplicative.ofAdd v.toAdd) ∈ center Q ↔ (line x).mkQ v.toAdd = 0
    rw [natural_central_iff Q f r hr e he hx hronto hein]
    exact (Submodule.Quotient.mk_eq_zero (line x)).symm
  let F := QuotientGroup.quotientKerEquivOfSurjective π hπ
  let i : Multiplicative (pointQuotient x) →* (Q ⧸ center Q) :=
    (QuotientGroup.lift _ j hj.ge).comp F.symm.toMonoidHom
  have hi : Function.Injective i :=
    ((QuotientGroup.injective_lift_iff _ j hj.ge).mpr hj.symm).comp F.symm.injective
  have hiπ (v : Multiplicative (Space 4)) : i (π v) = j v := by
    change QuotientGroup.lift _ j hj.ge (F.symm (F (QuotientGroup.mk' _ v))) = _
    rw [F.symm_apply_apply]
    rfl
  let a : D →* BinaryLinear.GL (pointQuotient x) := (pointQuotientAction x).comp f
  have ha : Function.Surjective a := (quotientAction_surjective x).comp hf
  have ih (d : D) (v : Multiplicative (pointQuotient x)) :
      centralAction Q d (i v) = i (Multiplicative.ofAdd (a d v.toAdd)) := by
    obtain ⟨w, rfl⟩ := hπ v
    have haπ : Multiplicative.ofAdd (a d (π w).toAdd) =
        π (Multiplicative.ofAdd ((f d).val w.toAdd)) := rfl
    rw [haπ, hiπ, hiπ]
    change centralAction Q d (QuotientGroup.mk' _ (e w)) =
      QuotientGroup.mk' _ (e (Multiplicative.ofAdd ((f d).val w.toAdd)))
    rw [centralAction_mk]
    exact congrArg (QuotientGroup.mk' _) (he d w.toAdd)
  let p0 := dualProjection Q r hx
  have hp0 : Function.Surjective p0 :=
    (displacementDual hx).toAddEquiv.toMultiplicative.surjective.comp
      ((kernelDisplacementEquiv x).surjective.comp hronto)
  have hz : center Q ≤ p0.ker := by
    intro z hz
    have hzr : r z = 1 := center_le_radical_ker Q f r hr e he hein hz
    change (displacementDual hx).toAddEquiv.toMultiplicative
      (kernelDisplacementEquiv x (r z)) = 1
    rw [hzr, map_one, map_one]
  let p : (Q ⧸ center Q) →* Multiplicative (Module.Dual (ZMod 2) (pointQuotient x)) :=
    QuotientGroup.lift _ p0 hz
  have hp : Function.Surjective p := QuotientGroup.lift_surjective_of_surjective _ _ hp0 _
  have ph (d : D) (c : Q ⧸ center Q) :
      (p (centralAction Q d c)).toAdd = (a d).symm.dualMap (p c).toAdd := by
    induction c using Quotient.inductionOn with
    | h q =>
      change (p (centralAction Q d (QuotientGroup.mk' _ q))).toAdd = _
      rw [centralAction_mk]
      exact dualProjection_conj Q f r hr hx d q
  exact BinaryLinearThree.HomogeneousDouble.no_opposing_group_sections
    a ha (BinaryNaturalDual.VectorStabilizers.Pure.quotientCoordinates hx)
    σ (centralAction Q) E hE i hi ih p hp ph

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.SourceDistanceFourSections
