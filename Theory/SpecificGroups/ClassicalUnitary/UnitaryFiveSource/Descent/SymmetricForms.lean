module

public import Theory.SpecificGroups.PSp4Three.MatrixModel
public import Theory.LinearAlgebra.AlternatingFinrank
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.Two

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Symmetric five-dimensional forms in characteristic two

Over a finite binary field, the square root of the self-pairing is a linear
functional. Its representing vector has norm one: otherwise adding the square
of that functional gives a nondegenerate alternating form in odd dimension.
The orthogonal complement is therefore an alternating four-space. A symplectic
basis and the explicit identity-form coordinates give a congruence to the
five-dimensional identity matrix, including over the field with two elements.

This is the fixed-field Gram normalization used for unitary graph-cocycle
descent in Aschbacher--Smith F.4.29(2), printed p.289 of refs/quasithin.pdf.
It avoids a determinant-polynomial field-size bound, which would fail when
the unitary dimension and q+1 are both five.
-/

public section
open Matrix Module
noncomputable section
namespace Theory.SpecificGroups.UnitaryFive.Descent.SymmetricForms
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (B : LinearMap.BilinForm F V) (hs : B.IsSymm)

private def normRoot : V →ₗ[F] F where
  toFun x := (frobeniusEquiv F 2).symm (B x x)
  map_add' x y := by
    apply CharTwo.sq_injective
    simp only [frobeniusEquiv_symm_pow_p, CharTwo.add_sq]
    simp only [map_add, LinearMap.add_apply]
    rw [hs.eq y x]
    ring_nf
    simp [CharTwo.ofNat_eq_mod]
  map_smul' a x := by
    apply CharTwo.sq_injective
    simp only [frobeniusEquiv_symm_pow_p, smul_eq_mul, mul_pow]
    simp [map_smul, LinearMap.smul_apply, smul_eq_mul, pow_two, mul_assoc]

omit [FiniteDimensional F V] in
private theorem normRoot_sq (x : V) : (normRoot B hs x)^2 = B x x :=
  frobeniusEquiv_symm_pow_p F 2 _

private def axis (hn : B.Nondegenerate) : V := (B.toDual hn).symm (normRoot B hs)

private theorem axis_pair (hn : B.Nondegenerate) (x : V) :
    B (axis B hs hn) x = normRoot B hs x :=
  LinearMap.BilinForm.apply_toDual_symm_apply _ _

private theorem axis_norm (hn : B.Nondegenerate) (hdim : Module.finrank F V = 5) :
    normRoot B hs (axis B hs hn) = 1 := by
  by_contra h
  let A : LinearMap.BilinForm F V := B +
    (LinearMap.mk₂ F (fun x y => normRoot B hs x * normRoot B hs y)
      (fun _ _ _ => by simp [add_mul]) (fun _ _ _ => by simp [mul_assoc])
      (fun _ _ _ => by simp [mul_add]) (fun _ _ _ => by simp [mul_left_comm]))
  have ha (x y : V) : A x y = B x y + normRoot B hs x * normRoot B hs y := rfl
  have hAlt : A.IsAlt := by
    intro x
    rw [ha, ←normRoot_sq B hs x, pow_two, CharTwo.add_self_eq_zero]
  have hN : A.Nondegenerate := by
    have hl : A.SeparatingLeft := by
      intro x hx
      have he : x = normRoot B hs x • axis B hs hn := by
        apply sub_eq_zero.mp
        apply hn.1
        intro y
        have hh := hx y
        rw [ha] at hh
        rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
          smul_eq_mul, axis_pair]
        exact sub_eq_zero.mpr (CharTwo.add_eq_zero.mp hh)
      have hr : normRoot B hs x = 0 := by
        have hh := congrArg (normRoot B hs) he
        simp only [map_smul, smul_eq_mul] at hh
        by_contra hx0
        apply h
        exact mul_left_cancel₀ hx0 (hh.symm.trans (mul_one _).symm)
      simpa only [hr, zero_smul] using he
    exact ⟨hl, fun x hx => hl x (fun y => hAlt.eq_iff.mpr (hx y))⟩
  have hp := AlternatingForm.even_finrank A hAlt hN
  rw [hdim] at hp
  obtain ⟨k, hk⟩ := hp
  omega

private def split (hn : B.Nondegenerate) (hdim : Module.finrank F V = 5) :
    V ≃ₗ[F] (normRoot B hs).ker × F where
  toFun x := (⟨x - normRoot B hs x • axis B hs hn, by
    simp [LinearMap.mem_ker, map_sub, axis_norm B hs hn hdim]⟩, normRoot B hs x)
  invFun x := x.1.val + x.2 • axis B hs hn
  left_inv x := by simp
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      have hx : normRoot B hs x.1.val = 0 := x.1.property
      simp [hx, axis_norm B hs hn hdim]
    · have hx : normRoot B hs x.1.val = 0 := x.1.property
      simp [hx, axis_norm B hs hn hdim]
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      simp only [map_add, add_smul, Prod.fst_add, Submodule.coe_add]
      abel
    · exact map_add _ _ _
  map_smul' a x := by
    apply Prod.ext
    · apply Subtype.ext
      simp [smul_sub, smul_smul]
    · exact map_smul _ _ _

omit [FiniteDimensional F V] in
private theorem complement_alt : (B.restrict (normRoot B hs).ker).IsAlt := by
  intro x
  change B x.val x.val = 0
  rw [←normRoot_sq B hs x.val, show normRoot B hs x.val = 0 from x.property]
  exact zero_pow (by decide)

private theorem complement_nondegenerate (hn : B.Nondegenerate)
    (hdim : Module.finrank F V = 5) :
    (B.restrict (normRoot B hs).ker).Nondegenerate := by
  have hl : (B.restrict (normRoot B hs).ker).SeparatingLeft := by
    intro x hx
    apply Subtype.ext
    apply hn.1 x.val
    intro y
    obtain ⟨⟨w,a⟩,rfl⟩ := (split B hs hn hdim).symm.surjective y
    have hw : B x.val w.val = 0 := hx w
    change B x.val (w.val + a • axis B hs hn) = 0
    rw [map_add, map_smul, hw, hs.eq x.val (axis B hs hn), axis_pair,
      show normRoot B hs x.val = 0 from x.property]
    simp
  exact ⟨hl, fun x hx => hl x (fun y => hs.eq x.val y.val ▸ hx y)⟩

private theorem split_form (hn : B.Nondegenerate) (hdim : Module.finrank F V = 5)
    (x y : (normRoot B hs).ker × F) :
    B ((split B hs hn hdim).symm x) ((split B hs hn hdim).symm y) =
      B x.1.val y.1.val + x.2 * y.2 := by
  have hx : normRoot B hs x.1.val = 0 := x.1.property
  have hy : normRoot B hs y.1.val = 0 := y.1.property
  have hc : B (axis B hs hn) (axis B hs hn) = 1 :=
    (axis_pair B hs hn _).trans (axis_norm B hs hn hdim)
  change B (x.1.val + x.2 • axis B hs hn) (y.1.val + y.2 • axis B hs hn) = _
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hs.eq x.1.val (axis B hs hn), axis_pair, axis_pair, hx, hy, hc]
  ring

private def standardSplit (hn : B.Nondegenerate) (hdim : Module.finrank F V = 5) :
    V ≃ₗ[F] Matrix.PSp4Three.Vector 2 F × F := by
  have hd : Module.finrank F (normRoot B hs).ker = 4 := by
    have hh := (split B hs hn hdim).finrank_eq
    rw [hdim, Module.finrank_prod, Module.finrank_self] at hh
    omega
  let e := Classical.choice (Matrix.PSp4Three.exists_isometry 2
    (B.restrict (normRoot B hs).ker) (complement_alt B hs)
    (complement_nondegenerate B hs hn hdim) hd)
  exact (split B hs hn hdim).trans (e.toLinearEquiv.prodCongr (LinearEquiv.refl F F))

private theorem standardSplit_form (hn : B.Nondegenerate) (hdim : Module.finrank F V = 5)
    (x y : V) :
    Matrix.PSp4Three.form (standardSplit B hs hn hdim x).1
      (standardSplit B hs hn hdim y).1 +
      (standardSplit B hs hn hdim x).2 * (standardSplit B hs hn hdim y).2 = B x y := by
  dsimp only [standardSplit, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply]
  simp only [LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv,
    LinearMap.BilinForm.IsometryEquiv.map_app]
  exact (split_form B hs hn hdim _ _).symm.trans (by simp)

private def coordinates : (Matrix.PSp4Three.Vector 2 F × F) ≃ₗ[F] (Fin 5 → F) where
  toFun x := ![x.1 (.inl 0)+x.1 (.inr 1)+x.2,
    x.1 (.inl 0)+x.1 (.inr 0)+x.1 (.inr 1)+x.2,
    x.1 (.inl 1)+x.2, x.1 (.inl 1)+x.1 (.inr 1)+x.2,
    x.1 (.inr 0)+x.1 (.inr 1)+x.2]
  invFun v := (Sum.elim ![v 1+v 4,v 0+v 1+v 3+v 4] ![v 0+v 1,v 2+v 3],
    v 0+v 1+v 2+v 3+v 4)
  left_inv x := by
    apply Prod.ext
    · funext i
      rcases i with i | i <;> fin_cases i <;> simp <;>
        ring_nf <;> simp [CharTwo.ofNat_eq_mod]
    · simp
      ring_nf
      simp [CharTwo.ofNat_eq_mod]
  right_inv v := by
    funext i
    fin_cases i <;> simp <;> ring_nf <;> simp [CharTwo.ofNat_eq_mod]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by ext i; fin_cases i <;> simp <;> ring

omit [Finite F] in
private theorem coordinates_dot (x y : Matrix.PSp4Three.Vector 2 F × F) :
    dotProduct (coordinates x) (coordinates y) =
      Matrix.PSp4Three.form x.1 y.1+x.2*y.2 := by
  simp [coordinates,dotProduct,Fin.sum_univ_succ,Matrix.PSp4Three.form_apply,
    CharTwo.sub_eq_add]
  ring_nf
  simp [CharTwo.ofNat_eq_mod]

include hs in
theorem exists_isometry_identity (hn : B.Nondegenerate) (hdim : Module.finrank F V = 5) :
    ∃ e : V ≃ₗ[F] (Fin 5 → F), ∀ x y, dotProduct (e x) (e y) = B x y := by
  refine ⟨(standardSplit B hs hn hdim).trans coordinates, ?_⟩
  intro x y
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, coordinates_dot]
  exact standardSplit_form B hs hn hdim x y

theorem exists_congruence_identity (S : Matrix (Fin 5) (Fin 5) F)
    (hS : S.transpose = S) (hd : S.det ≠ 0) :
    ∃ C : GL (Fin 5) F, C.val.transpose * S * C.val = 1 := by
  have hsym : S.toBilin'.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hS
  obtain ⟨e,he⟩ := exists_isometry_identity S.toBilin' hsym
    (LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' S hd) (by simp)
  let C := (LinearMap.toMatrix' e.symm.toLinearMap)
  have hc : C.transpose * S * C = 1 := by
    ext i j
    rw [←Matrix.toBilin'_single (C.transpose * S * C) i j,
      ←Matrix.toBilin'_comp]
    change S.toBilin' (C *ᵥ Pi.single i 1) (C *ᵥ Pi.single j 1) = (1 : Matrix _ _ F) i j
    have hcol (k : Fin 5) : C *ᵥ Pi.single k 1 = e.symm (Pi.single k 1) := by
      simp only [Matrix.mulVec_single, MulOpposite.op_one, one_smul]
      rfl
    rw [hcol, hcol, ←he]
    simp [dotProduct, Pi.single_apply, Matrix.one_apply, eq_comm]
  have hdC : C.det ≠ 0 := by
    intro h
    have hh := congrArg Matrix.det hc
    simp [Matrix.det_mul, Matrix.det_transpose, h] at hh
  exact ⟨GeneralLinearGroup.mkOfDetNeZero C hdC, hc⟩

end Theory.SpecificGroups.UnitaryFive.Descent.SymmetricForms
