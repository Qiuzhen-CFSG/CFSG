module

public import Theory.Representation.SL2.BinarySmallModels
public import Theory.Representation.OrthogonalFourMinusFirstCohomology
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Basic
public import Theory.SpecificGroups.PSL2.InvolutionFusion
public import Theory.SpecificGroups.PSL2.AutomorphismModel

/-!
# Hermitian binary involution displacement

For the literal Hermitian model over `Field r`, every involution has moved
space of binary dimension at least `2r`.  The upper transvection calculation
uses coordinates over the fixed field: its displacement contains the image of
an injective map from two fixed-field coordinates.  Involution fusion in the
actual projective quotient, together with the characteristic-two quotient
isomorphism, transports this rank to every involution.

This is the intrinsic model calculation used in GLS, volume 3, G.9.3(7),
printed pp.353--357 (and the rank-one exclusion at 15.3.58, p.1149).
-/

@[expose] public section

open scoped MatrixGroups
open Matrix
open Representation
open Representation.RankTwo
open Representation.SL2
open Representation.SL2.BinarySmall
open Representation.OrthogonalFourMinus.FiniteModel

attribute [local instance] BinarySmall.fixedBinaryAlgebra BinarySmall.spaceBinaryModule

namespace Representation.SL2.BinarySmall.HermitianInvolution
noncomputable section
variable (r : ℕ) [NeZero r]

private abbrev Coeff (r : ℕ) := fixedField r
private abbrev Ext (r : ℕ) := Representation.OrthogonalFourMinus.FiniteModel.Field r
private abbrev MatGroup (r : ℕ) := Matrix.SpecialLinearGroup (Fin 2) (Ext r)

private abbrev hij : (0 : Fin 2) ≠ 1 := by decide
private abbrev u (r : ℕ) : MatGroup r := Matrix.SpecialLinearGroup.transvection hij 1

omit [NeZero r] in
private lemma u_sq : u r ^ 2 = 1 := by
  rw [pow_two, ← Matrix.SpecialLinearGroup.transvection_add hij 1 1]
  have htwo : (1 : Ext r) + 1 = 0 := by
    calc
      (1 : Ext r) + 1 = (2 : Ext r) := by norm_num
      _ = 0 := CharP.cast_eq_zero (Ext r) 2
  rw [htwo, Matrix.SpecialLinearGroup.transvection_coeff_zero]

omit [NeZero r] in
private lemma u_ne_one : u r ≠ 1 := by
  intro h
  have hh := congrArg (fun A : MatGroup r => A.val 0 1) h
  simp [u, Matrix.SpecialLinearGroup.transvection_coe] at hh

omit [NeZero r] in
private lemma u_order : orderOf (u r) = 2 := by
  apply (orderOf_eq_prime_iff (p := 2)).mpr
  exact ⟨u_sq r, u_ne_one r⟩

private lemma upper_action_apply (X : Space r) :
    (action r (u r) X).val =
      !![X.val 0 0 + X.val 1 0 + X.val 0 1 + X.val 1 1,
         X.val 0 1 + X.val 1 1;
         X.val 1 0 + X.val 1 1, X.val 1 1] := by
  rw [action_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u, Matrix.SpecialLinearGroup.transvection_coe,
      OrthogonalFourMinus.adjoint, Matrix.mul_apply, Fin.sum_univ_two, map_add]
  all_goals ring

omit [NeZero r] in
private lemma d_ne_zero (t : Ext r) (ht : conjugation r t ≠ t) :
    t + conjugation r t ≠ 0 := by
  intro h
  apply ht
  apply CharTwo.add_eq_zero.mp
  simpa [add_comm] using h

private def coordInput (t : Ext r) : (Coeff r × Coeff r) →ₗ[Coeff r]
    ((Coeff r × Coeff r) × Ext r) where
  toFun p := ((0, p.2), ((p.1 + p.2).val * (t + conjugation r t)⁻¹) * t)
  map_add' p q := by
    ext <;> simp
    ring
  map_smul' c p := by
    ext <;> simp [Subfield.smul_def, smul_eq_mul]
    ring

private def input (t : Ext r) : (Coeff r × Coeff r) →ₗ[Coeff r] Space r :=
  (coordinates r).symm.toLinearMap.comp (coordInput r t)

private lemma upper_displacement_coordinates (t : Ext r) (p : Coeff r × Coeff r)
    (ht : conjugation r t ≠ t) :
    coordinates r ((action r (u r) - (LinearMap.id : Space r →ₗ[Coeff r] Space r))
      (input r t p)) = ((p.1, (0 : Coeff r)), p.2.val) := by
  let d : Ext r := t + conjugation r t
  have hd : d ≠ 0 := d_ne_zero r t ht
  have hdc : conjugation r d = d := by
    dsimp [d]
    rw [map_add, conjugation_involutive]
    exact add_comm _ _
  have hv : ((action r (u r) - (LinearMap.id : Space r →ₗ[Coeff r] Space r))
      (input r t p)) = (coordinates r).symm ((p.1, 0), p.2.val) := by
    change ((action r (u r) - (LinearMap.id : Space r →ₗ[Coeff r] Space r))
        ((coordinates r).symm ((0, p.2), ((p.1 + p.2).val * d⁻¹) * t))) =
        (coordinates r).symm ((p.1, 0), p.2.val)
    have hsub : (action r (u r) - (LinearMap.id : Space r →ₗ[Coeff r] Space r)) =
        action r (u r) + LinearMap.id := by
      apply LinearMap.ext
      intro Y
      change (action r (u r) Y - Y) = action r (u r) Y + Y
      rw [sub_eq_add_neg]
      have hneg : -Y = Y := by
        apply Subtype.ext
        ext i j
        exact CharTwo.neg_eq _
      change action r (u r) Y + (-Y) = action r (u r) Y + Y
      rw [hneg]
    rw [hsub]
    apply Subtype.ext
    change (action r (u r) ((coordinates r).symm ((0, p.2),
      ((p.1 + p.2).val * d⁻¹) * t))).val +
      ((coordinates r).symm ((0, p.2), ((p.1 + p.2).val * d⁻¹) * t)).val = _
    rw [upper_action_apply]
    simp only [coordinates_symm_val]
    ext i j
    have htwo : (2 : Ext r) = 0 := CharP.cast_eq_zero (Ext r) 2
    have hthree : (3 : Ext r) = 1 := by
      calc
        (3 : Ext r) = 2 + 1 := by norm_num
        _ = 1 := by rw [htwo]; simp
    have hp₁ : conjugation r p.1.val = p.1.val := p.1.property
    have hp₂ : conjugation r p.2.val = p.2.val := p.2.property
    have hmul₁ : p.2.val * conjugation r t * (2 : Ext r) = 0 := by
      rw [mul_two]
      exact (CharTwo.add_eq_zero).2 rfl
    have hmul₂ : p.2.val * t * (2 : Ext r) = 0 := by
      rw [mul_two]
      exact (CharTwo.add_eq_zero).2 rfl
    have hmul₃ : p.1.val * t * (2 : Ext r) = 0 := by
      rw [mul_two]
      exact (CharTwo.add_eq_zero).2 rfl
    have hmul₄ : p.1.val * conjugation r t * (2 : Ext r) = 0 := by
      rw [mul_two]
      exact (CharTwo.add_eq_zero).2 rfl
    have hmul₅ : p.2.val * t * (3 : Ext r) = p.2.val * t := by
      rw [show (3 : Ext r) = 2 + 1 by norm_num, mul_add, hmul₂]
      simp
    have hmul₆ : p.2.val * conjugation r t * (3 : Ext r) =
        p.2.val * conjugation r t := by
      rw [show (3 : Ext r) = 2 + 1 by norm_num, mul_add]
      have hz' : p.2.val * conjugation r t * (2 : Ext r) = 0 := by
        rw [mul_two]
        exact (CharTwo.add_eq_zero).2 rfl
      rw [hz']
      simp
    have hmul₇ : p.2.val * ((1 : Ext r) + 1) = 0 := by
      rw [mul_add, mul_one, CharTwo.add_eq_zero]
    fin_cases i <;> fin_cases j <;> simp
    all_goals first | rw [hp₁] | skip
    all_goals first | rw [hp₂] | skip
    all_goals first | rw [hdc] | skip
    all_goals field_simp [hd]
    all_goals first
      | linear_combination hmul₁ + hmul₂
      | linear_combination hmul₃ + hmul₅
      | linear_combination hmul₄ + hmul₆
      | exact hmul₇
  exact congrArg (coordinates r) hv

private lemma upper_injective (t : Ext r) (ht : conjugation r t ≠ t) :
    Function.Injective ((action r (u r) - LinearMap.id).comp (input r t)) := by
  intro p q h
  have hc := upper_displacement_coordinates r t p ht
  have hc' := upper_displacement_coordinates r t q ht
  have h' := h
  change ((action r (u r) - (LinearMap.id : Space r →ₗ[Coeff r] Space r)) (input r t p)) =
      ((action r (u r) - (LinearMap.id : Space r →ₗ[Coeff r] Space r)) (input r t q)) at h'
  rw [h'] at hc
  have he : ((p.1, (0 : Coeff r)), p.2.val) =
      ((q.1, (0 : Coeff r)), q.2.val) := hc.symm.trans hc'
  have hp := congrArg Prod.fst he
  have hp1 := congrArg Prod.fst hp
  have hp2 := congrArg Prod.snd hp
  have hz := congrArg id (congrArg Prod.snd he)
  exact Prod.ext hp1 (Subtype.ext hz)

set_option maxHeartbeats 200000 in
private theorem upper_rank_explicit (r : ℕ) [NeZero r] :
    2 * r ≤ Module.finrank (ZMod 2) (LinearMap.range
      (((action r (u r)).toAddMonoidHom.toZModLinearMap 2) -
        (LinearMap.id : Space r →ₗ[ZMod 2] Space r))) := by
  obtain ⟨t, ht⟩ := exists_conjugation_ne r
  let f : (Coeff r × Coeff r) →ₗ[Coeff r] Space r :=
    ((action r (u r) - (LinearMap.id : Space r →ₗ[Coeff r] Space r)).comp (input r t))
  let fz : (Coeff r × Coeff r) →ₗ[ZMod 2] Space r := f.restrictScalars (ZMod 2)
  have hf : Function.Injective f := upper_injective r t ht
  have hfz : Function.Injective fz := by
    intro x y hxy
    apply hf
    exact hxy
  have hfrz : Module.finrank (ZMod 2) (LinearMap.range fz) = 2 * r := by
    rw [LinearMap.finrank_range_of_inj hfz, Module.finrank_prod,
      finrank_binary_fixedField]
    omega
  have hle : LinearMap.range fz ≤ LinearMap.range
      (((action r (u r)).toAddMonoidHom.toZModLinearMap 2) -
        (LinearMap.id : Space r →ₗ[ZMod 2] Space r)) := by
    rintro y ⟨x, rfl⟩
    refine ⟨input r t x, ?_⟩
    change ((action r (u r) - (LinearMap.id : Space r →ₗ[Coeff r] Space r))
      (input r t x)) = fz x
    rfl
  have hfin : Module.finrank (ZMod 2) (LinearMap.range fz) ≤
      Module.finrank (ZMod 2) (LinearMap.range
        (((action r (u r)).toAddMonoidHom.toZModLinearMap 2) -
          (LinearMap.id : Space r →ₗ[ZMod 2] Space r))) :=
    Submodule.finrank_mono hle
  calc
    2 * r = Module.finrank (ZMod 2) (LinearMap.range fz) := hfrz.symm
    _ ≤ _ := hfin

private theorem upper_rank (r : ℕ) [NeZero r] :
    2 * r ≤ Module.finrank (ZMod 2)
      (movedSpace (hermitian r) (u r)) := by
  change 2 * r ≤ Module.finrank (ZMod 2) (LinearMap.range
    (((action r (u r)).toAddMonoidHom.toZModLinearMap 2) -
      (LinearMap.id : Space r →ₗ[ZMod 2] Space r)))
  exact upper_rank_explicit r

private def actionEquiv (d : MatGroup r) : Space r ≃ₗ[ZMod 2] Space r :=
  LinearEquiv.ofBijective ((action r d).toAddMonoidHom.toZModLinearMap 2) (by
    constructor
    · intro x y hxy
      change action r d x = action r d y at hxy
      have h := congrArg (fun z => action r d⁻¹ z) hxy
      simpa only [← Module.End.mul_apply, ← (action r).map_mul, inv_mul_cancel,
        (action r).map_one, Module.End.one_apply] using h
    · intro y
      refine ⟨action r d⁻¹ y, ?_⟩
      change action r d (action r d⁻¹ y) = y
      simp only [← Module.End.mul_apply, ← (action r).map_mul, mul_inv_cancel,
        (action r).map_one, Module.End.one_apply] )

private lemma finrank_conj (g d : MatGroup r) :
    Module.finrank (ZMod 2) (movedSpace (hermitian r) (d * g * d⁻¹)) =
      Module.finrank (ZMod 2) (movedSpace (hermitian r) g) := by
  let e : MatGroup r ≃* MatGroup r := MulAut.conj d
  let f : Space r ≃ₗ[ZMod 2] Space r := actionEquiv r d
  have hf : ∀ x z, f (hermitian r x z) = hermitian r (e x) (f z) := by
    intro x z
    change action r d (action r x z) = action r (d * x * d⁻¹) (action r d z)
    simp only [← Module.End.mul_apply, ← (action r).map_mul, mul_assoc,
      inv_mul_cancel, mul_one]
  exact (finrank_movedSpace_transport (hermitian r) (hermitian r) e f hf g).symm

theorem rank_ge
    (g : Matrix.SpecialLinearGroup (Fin 2)
      (Representation.OrthogonalFourMinus.FiniteModel.Field r))
    (hg : orderOf g = 2) :
    2 * r ≤ Module.finrank (ZMod 2) (movedSpace (hermitian r) g) := by
  let e := Theory.PSL2.sl2QuotientEquiv (Ext r)
  have hc := Theory.PSL2.involutions_isConj (e g) (e (u r))
    ((e.orderOf_eq g).trans hg) ((e.orderOf_eq (u r)).trans (u_order r))
  have hs : IsConj g (u r) := by
    simpa only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using
      e.symm.toMonoidHom.map_isConj hc
  obtain ⟨d, hd⟩ := isConj_iff.mp hs
  calc
    2 * r ≤ Module.finrank (ZMod 2) (movedSpace (hermitian r) (u r)) := upper_rank r
    _ = Module.finrank (ZMod 2) (movedSpace (hermitian r) g) := by
      rw [← hd]
      exact finrank_conj r g d


end
end Representation.SL2.BinarySmall.HermitianInvolution
end
