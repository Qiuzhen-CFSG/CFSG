module

public import Theory.AlgebraicGroup.RootSystems.SplitQuadraticConjugationGeneration
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.Tactic

/-!
# Symmetry factorization over finite coefficient fields

The hyperbolic-basis induction from
`SplitQuadraticConjugationGeneration.lean` works over any finite field of
cardinality greater than two. This adaptation retains that module's proof
and conjugation convention, replacing its infinitude argument by the exact
cardinality bound: an isotropic Eichler parameter is a sum of two anisotropic
parameters by choosing a scalar outside a set of at most two elements.

The other steps move an isotropic vector, fix its hyperbolic partner with
Eichler transformations, and lift the induction on the hyperbolic tail.
Products act by foldr, with the rightmost symmetry first.
This is the characteristic-free split Cartan–Dieudonné argument used in the
orthogonal realization of GLS3 §2.7 and §§1.10–1.12.
-/

universe u
open scoped BigOperators
namespace Theory.AlgebraicGroup.FiniteSymmetryFactorization
open Theory.AlgebraicGroup
variable {k V : Type u} [Field k]
variable [AddCommGroup V] [Module k V]
variable {Q : QuadraticForm k V}

private lemma conjugationSymmetry_maps_isotropic (Q : QuadraticForm k V)
    {x y : V} (hx : Q x = 0) (hy : Q y = 0)
    (hxy : QuadraticMap.polar Q x y ≠ 0) :
    conjugationSymmetry Q (x + y) (by
      rw [QuadraticMap.map_add Q, hx, hy, zero_add, zero_add]
      exact hxy) x = y := by
  rw [conjugationSymmetry_apply]
  have hsum : Q (x + y) = QuadraticMap.polar Q x y := by
    rw [QuadraticMap.map_add Q, hx, hy, zero_add, zero_add]
  have hpolar : QuadraticMap.polar Q (x + y) x =
      QuadraticMap.polar Q x y := by
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_self, hx,
      smul_zero, zero_add, QuadraticMap.polar_comm]
  rw [hsum, hpolar, inv_mul_cancel₀ hxy, one_smul]
  abel

private abbrev AnisotropicVector (Q : QuadraticForm k V) :=
  {a : V // Q a ≠ 0}

private noncomputable def symmetryProduct (Q : QuadraticForm k V)
    (as : List (AnisotropicVector Q)) : V ≃ₗ[k] V :=
  (as.map fun a : AnisotropicVector Q =>
    (conjugationSymmetry Q (a : V) a.property).toLinearEquiv).prod

private lemma symmetryProduct_apply (Q : QuadraticForm k V)
    (as : List (AnisotropicVector Q)) (x : V) :
    symmetryProduct Q as x =
      as.foldr (fun (a : AnisotropicVector Q) y =>
        conjugationSymmetry Q (a : V) a.property y) x := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      change conjugationSymmetry Q (a : V) a.property (symmetryProduct Q as x) = _
      simpa using congrArg (fun y => conjugationSymmetry Q (a : V) a.property y) ih

private lemma symmetryProduct_preserves (Q : QuadraticForm k V)
    (as : List (AnisotropicVector Q)) (x : V) :
    Q (symmetryProduct Q as x) = Q x := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      change Q (conjugationSymmetry Q (a : V) a.property (symmetryProduct Q as x)) = Q x
      rw [(conjugationSymmetry Q (a : V) a.property).map_app, ih]

private lemma symmetryProduct_append (Q : QuadraticForm k V)
    (as bs : List (AnisotropicVector Q)) :
    symmetryProduct Q (as ++ bs) = symmetryProduct Q as * symmetryProduct Q bs := by
  simp [symmetryProduct, List.map_append]

private lemma symmetryProduct_reverse_left (Q : QuadraticForm k V)
    (as : List (AnisotropicVector Q)) (x : V) :
    symmetryProduct Q as.reverse (symmetryProduct Q as x) = x := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      rw [List.reverse_cons, symmetryProduct_append]
      change symmetryProduct Q as.reverse
        (conjugationSymmetry Q (a : V) a.property
          (conjugationSymmetry Q (a : V) a.property (symmetryProduct Q as x))) = x
      rw [conjugationSymmetry_involutive]
      exact ih

private def hyperbolicPlaneForm : QuadraticForm k (k × k) where
  toFun x := x.1 * x.2
  toFun_smul := by intros; simp; ring
  exists_companion' := by
    refine ⟨LinearMap.mk₂ k (fun x y => x.1 * y.2 + y.1 * x.2) ?_ ?_ ?_ ?_, ?_⟩
    · intros; simp; ring
    · intros; simp; ring
    · intros; simp; ring
    · intros; simp; ring
    · intros; simp; ring

@[simp] private lemma hyperbolicPlaneForm_apply (x : k × k) :
    hyperbolicPlaneForm x = x.1 * x.2 := rfl

@[simp] private lemma hyperbolicPlaneForm_polar (x y : k × k) :
    QuadraticMap.polar hyperbolicPlaneForm x y =
      x.1 * y.2 + y.1 * x.2 := by
  simp [QuadraticMap.polar]
  ring

private abbrev hyperbolicSumForm {W : Type u} [AddCommGroup W] [Module k W]
    (R : QuadraticForm k W) : QuadraticForm k ((k × k) × W) :=
  hyperbolicPlaneForm.prod R

@[simp] private lemma hyperbolicSumForm_apply
    {W : Type u} [AddCommGroup W] [Module k W]
    (R : QuadraticForm k W) (x : (k × k) × W) :
    hyperbolicSumForm R x = x.1.1 * x.1.2 + R x.2 := by
  rfl

@[simp] private lemma hyperbolicSumForm_polar
    {W : Type u} [AddCommGroup W] [Module k W]
    (R : QuadraticForm k W) (x y : (k × k) × W) :
    QuadraticMap.polar (hyperbolicSumForm R) x y =
      x.1.1 * y.1.2 + y.1.1 * x.1.2 + QuadraticMap.polar R x.2 y.2 := by
  simp [QuadraticMap.polar]
  ring

private def hyperbolicHead
    {W : Type u} [AddCommGroup W] [Module k W] : (k × k) × W :=
  ((1, 0), 0)

private def hyperbolicPartner
    {W : Type u} [AddCommGroup W] [Module k W] : (k × k) × W :=
  ((0, 1), 0)

private def hyperbolicTail
    {W : Type u} [AddCommGroup W] [Module k W] (w : W) : (k × k) × W :=
  ((0, 0), w)

@[simp] private lemma hyperbolicHead_form
    {W : Type u} [AddCommGroup W] [Module k W]
    (R : QuadraticForm k W) :
    hyperbolicSumForm R (hyperbolicHead (k := k) (W := W)) = 0 := by
  simp [hyperbolicHead]

@[simp] private lemma hyperbolicPartner_form
    {W : Type u} [AddCommGroup W] [Module k W]
    (R : QuadraticForm k W) :
    hyperbolicSumForm R (hyperbolicPartner (k := k) (W := W)) = 0 := by
  simp [hyperbolicPartner]

@[simp] private lemma hyperbolicTail_form
    {W : Type u} [AddCommGroup W] [Module k W]
    (R : QuadraticForm k W) (w : W) :
    hyperbolicSumForm R (hyperbolicTail (k := k) w) = R w := by
  simp [hyperbolicTail]

private lemma isometry_polar
    {W : Type u} [AddCommGroup W] [Module k W]
    {R : QuadraticForm k W} (g : R.IsometryEquiv R) (x y : W) :
    QuadraticMap.polar R (g x) (g y) = QuadraticMap.polar R x y := by
  simp only [QuadraticMap.polar, ← map_add, g.map_app]

private lemma move_isotropic_to_head
    {W : Type u} [AddCommGroup W] [Module k W]
    (R : QuadraticForm k W)
    (hpolar : Function.Injective R.polarBilin)
    (u : (k × k) × W)
    (huq : hyperbolicSumForm R u = 0) (hu : u ≠ 0) :
    ∃ as : List (AnisotropicVector (hyperbolicSumForm R)),
      symmetryProduct (hyperbolicSumForm R) as u =
        hyperbolicHead (k := k) (W := W) := by
  let e := hyperbolicHead (k := k) (W := W)
  by_cases hb : u.1.2 = 0
  · by_cases hw : u.2 = 0
    · have ha : u.1.1 ≠ 0 := by
        intro ha
        apply hu
        rcases u with ⟨⟨a, b⟩, w⟩
        simp only at ha hb hw
        simp [ha, hb, hw]
      let z : (k × k) × W := ((0, 1), 0)
      have hzq : hyperbolicSumForm R z = 0 := by simp [z]
      have huz : QuadraticMap.polar (hyperbolicSumForm R) u z ≠ 0 := by
        simpa [z, hb, hw] using ha
      have hze : QuadraticMap.polar (hyperbolicSumForm R) z e ≠ 0 := by
        simp [z, e, hyperbolicHead]
      let az : AnisotropicVector (hyperbolicSumForm R) :=
        ⟨u + z, by
          rw [QuadraticMap.map_add (hyperbolicSumForm R), huq, hzq,
            zero_add, zero_add]
          exact huz⟩
      let ae : AnisotropicVector (hyperbolicSumForm R) :=
        ⟨z + e, by
          rw [QuadraticMap.map_add (hyperbolicSumForm R), hzq,
            hyperbolicHead_form, zero_add, zero_add]
          exact hze⟩
      refine ⟨[ae, az], ?_⟩
      change conjugationSymmetry (hyperbolicSumForm R) (ae : (k × k) × W) ae.property
          (conjugationSymmetry (hyperbolicSumForm R) (az : (k × k) × W)
            az.property u) = e
      rw [show conjugationSymmetry (hyperbolicSumForm R) (az : (k × k) × W)
          az.property u = z from
        conjugationSymmetry_maps_isotropic (hyperbolicSumForm R) huq hzq huz]
      exact conjugationSymmetry_maps_isotropic (hyperbolicSumForm R) hzq
        (hyperbolicHead_form R) hze
    · have hfunctional : ∃ y : W, QuadraticMap.polar R u.2 y ≠ 0 := by
        by_contra h
        apply hw
        apply hpolar
        apply LinearMap.ext
        intro y
        have hy0 : QuadraticMap.polar R u.2 y = 0 := by
          by_contra hy
          exact h ⟨y, hy⟩
        simpa [QuadraticMap.polarBilin_apply_apply] using hy0
      obtain ⟨y, hy⟩ := hfunctional
      let c := (1 - u.1.1) * (QuadraticMap.polar R u.2 y)⁻¹
      let zw : W := c • y
      have hwz : QuadraticMap.polar R u.2 zw = 1 - u.1.1 := by
        simp only [zw, c, QuadraticMap.polar_smul_right, smul_eq_mul]
        field_simp [hy]
      let z : (k × k) × W := ((-R zw, 1), zw)
      have hzq : hyperbolicSumForm R z = 0 := by simp [z]
      have huz : QuadraticMap.polar (hyperbolicSumForm R) u z ≠ 0 := by
        simp [z, hb, hwz]
      have hze : QuadraticMap.polar (hyperbolicSumForm R) z e ≠ 0 := by
        simp [z, e, hyperbolicHead]
      let az : AnisotropicVector (hyperbolicSumForm R) :=
        ⟨u + z, by
          rw [QuadraticMap.map_add (hyperbolicSumForm R), huq, hzq,
            zero_add, zero_add]
          exact huz⟩
      let ae : AnisotropicVector (hyperbolicSumForm R) :=
        ⟨z + e, by
          rw [QuadraticMap.map_add (hyperbolicSumForm R), hzq,
            hyperbolicHead_form, zero_add, zero_add]
          exact hze⟩
      refine ⟨[ae, az], ?_⟩
      change conjugationSymmetry (hyperbolicSumForm R) (ae : (k × k) × W) ae.property
          (conjugationSymmetry (hyperbolicSumForm R) (az : (k × k) × W)
            az.property u) = e
      rw [show conjugationSymmetry (hyperbolicSumForm R) (az : (k × k) × W)
          az.property u = z from
        conjugationSymmetry_maps_isotropic (hyperbolicSumForm R) huq hzq huz]
      exact conjugationSymmetry_maps_isotropic (hyperbolicSumForm R) hzq
        (hyperbolicHead_form R) hze
  · have hue : QuadraticMap.polar (hyperbolicSumForm R) u e ≠ 0 := by
      simpa [e, hyperbolicHead] using hb
    let a : AnisotropicVector (hyperbolicSumForm R) :=
      ⟨u + e, by
        rw [QuadraticMap.map_add (hyperbolicSumForm R), huq,
          hyperbolicHead_form, zero_add, zero_add]
        exact hue⟩
    refine ⟨[a], ?_⟩
    change conjugationSymmetry (hyperbolicSumForm R) (a : (k × k) × W) a.property u = e
    exact conjugationSymmetry_maps_isotropic (hyperbolicSumForm R) huq
      (hyperbolicHead_form R) hue

private def eichlerTransform
    {W : Type u} [AddCommGroup W] [Module k W]
    (R : QuadraticForm k W) (w : W) (x : (k × k) × W) : (k × k) × W :=
  ((x.1.1 - QuadraticMap.polar R w x.2 - R w * x.1.2, x.1.2),
    x.2 + x.1.2 • w)

@[simp] private lemma eichlerTransform_head
    {W : Type u} [AddCommGroup W] [Module k W]
    (R : QuadraticForm k W) (w : W) :
    eichlerTransform R w (hyperbolicHead (k := k) (W := W)) =
      hyperbolicHead (k := k) (W := W) := by
  simp [eichlerTransform, hyperbolicHead]

@[simp] private lemma eichlerTransform_partner
    {W : Type u} [AddCommGroup W] [Module k W]
    (R : QuadraticForm k W) (w : W) :
    eichlerTransform R w (hyperbolicPartner (k := k) (W := W)) =
      ((-R w, 1), w) := by
  simp [eichlerTransform, hyperbolicPartner]

private lemma eichlerTransform_add
    {W : Type u} [AddCommGroup W] [Module k W]
    (R : QuadraticForm k W) (u v : W) (x : (k × k) × W) :
    eichlerTransform R u (eichlerTransform R v x) =
      eichlerTransform R (u + v) x := by
  rcases x with ⟨⟨a, b⟩, x⟩
  apply Prod.ext
  · apply Prod.ext
    · dsimp only [eichlerTransform]
      rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
        QuadraticMap.polar_add_left, QuadraticMap.map_add R]
      simp only [smul_eq_mul]
      ring
    · rfl
  · simp only [eichlerTransform]
    module

private lemma eichlerTransform_neg_partner
    {W : Type u} [AddCommGroup W] [Module k W]
    (R : QuadraticForm k W) (w : W) :
    eichlerTransform R (-w) ((-R w, 1), w) =
      hyperbolicPartner (k := k) (W := W) := by
  apply Prod.ext
  · apply Prod.ext
    · simp only [eichlerTransform, hyperbolicPartner,
        QuadraticMap.polar_neg_left, QuadraticMap.polar_self,
        QuadraticMap.map_neg, one_smul]
      ring
    · simp [eichlerTransform, hyperbolicPartner]
  · simp [eichlerTransform, hyperbolicPartner]

private lemma eichlerTransform_factor_from_vector
    {W : Type u} [AddCommGroup W] [Module k W]
    (R : QuadraticForm k W) (r : W) (hr : R r ≠ 0) :
    ∃ as : List (AnisotropicVector (hyperbolicSumForm R)),
      ∀ x, symmetryProduct (hyperbolicSumForm R) as x =
        eichlerTransform R (-((R r)⁻¹) • r) x := by
  let ar : AnisotropicVector (hyperbolicSumForm R) :=
    ⟨hyperbolicTail (k := k) r, by
      simpa only [hyperbolicTail_form] using hr⟩
  let aer : AnisotropicVector (hyperbolicSumForm R) :=
    ⟨hyperbolicHead (k := k) (W := W) + hyperbolicTail (k := k) r, by
      rw [QuadraticMap.map_add (hyperbolicSumForm R), hyperbolicHead_form,
        hyperbolicTail_form]
      simpa [hyperbolicHead, hyperbolicTail] using hr⟩
  have hscaled : R ((R r)⁻¹ • r) = (R r)⁻¹ := by
    rw [QuadraticMap.map_smul]
    simp only [smul_eq_mul]
    field_simp [hr]
  refine ⟨[aer, ar], ?_⟩
  intro x
  rw [symmetryProduct_apply]
  simp only [List.foldr_cons, List.foldr_nil]
  rw [conjugationSymmetry_apply, conjugationSymmetry_apply]
  rcases x with ⟨⟨a, b⟩, x⟩
  apply Prod.ext
  · apply Prod.ext
    · simp [aer, ar, hyperbolicHead, hyperbolicTail, eichlerTransform,
        QuadraticMap.polar_self, hscaled]
      field_simp [hr]
      ring
    · simp [aer, ar, hyperbolicHead, hyperbolicTail, eichlerTransform,
        QuadraticMap.polar_self, hscaled]
  · simp [aer, ar, hyperbolicHead, hyperbolicTail, eichlerTransform,
      QuadraticMap.polar_self]
    field_simp [hr]
    module

private lemma eichlerTransform_factor_of_anisotropic
    {W : Type u} [AddCommGroup W] [Module k W]
    (R : QuadraticForm k W) (w : W) (hw : R w ≠ 0) :
    ∃ as : List (AnisotropicVector (hyperbolicSumForm R)),
      ∀ x, symmetryProduct (hyperbolicSumForm R) as x =
        eichlerTransform R w x := by
  let r : W := (-((R w)⁻¹)) • w
  have hrq : R r = (R w)⁻¹ := by
    simp [r, QuadraticMap.map_smul, hw]
  have hr : R r ≠ 0 := hrq.symm ▸ inv_ne_zero hw
  obtain ⟨as, has⟩ := eichlerTransform_factor_from_vector R r hr
  refine ⟨as, ?_⟩
  intro x
  rw [has]
  congr 2
  rw [hrq]
  simp only [r, inv_inv, smul_smul, neg_mul_neg]
  rw [mul_inv_cancel₀ hw, one_smul]

private lemma isotropic_eq_add_anisotropic
    {W : Type u} [AddCommGroup W] [Module k W]
    [Fintype k] [Fact (2 < Fintype.card k)] (R : QuadraticForm k W)
    (hpolar : Function.Injective R.polarBilin)
    (w : W) (hw : w ≠ 0) (hwq : R w = 0) :
    ∃ u v : W, u + v = w ∧ R u ≠ 0 ∧ R v ≠ 0 := by
  classical
  have hfunctional : ∃ z : W, QuadraticMap.polar R w z ≠ 0 := by
    by_contra h
    apply hw
    apply hpolar
    apply LinearMap.ext
    intro z
    have hz0 : QuadraticMap.polar R w z = 0 := by
      by_contra hz
      exact h ⟨z, hz⟩
    simpa [QuadraticMap.polarBilin_apply_apply] using hz0
  obtain ⟨z, hwz⟩ := hfunctional
  obtain ⟨y, hyq, hwy⟩ :
      ∃ y : W, R y ≠ 0 ∧ QuadraticMap.polar R w y ≠ 0 := by
    by_cases hzq : R z ≠ 0
    · exact ⟨z, hzq, hwz⟩
    · have hzq0 : R z = 0 := not_ne_iff.mp hzq
      refine ⟨z + w, ?_, ?_⟩
      · rw [QuadraticMap.map_add R, hzq0, hwq, zero_add, zero_add,
          QuadraticMap.polar_comm]
        exact hwz
      · simpa [QuadraticMap.polar_add_right, QuadraticMap.polar_self, hwq]
          using hwz
  have hsmall : ({0, QuadraticMap.polar R w y * (R y)⁻¹} : Finset k).card <
      (Finset.univ : Finset k).card := by
    have hle : ({0, QuadraticMap.polar R w y * (R y)⁻¹} : Finset k).card ≤ 2 :=
      le_trans (Finset.card_insert_le _ _) (by simp)
    simpa only [Finset.card_univ] using lt_of_le_of_lt hle Fact.out
  obtain ⟨t, _, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  have ht0 : t ≠ 0 := by
    intro ht0
    apply ht
    simp [ht0]
  have htbad : t ≠ QuadraticMap.polar R w y * (R y)⁻¹ := by
    intro htbad
    apply ht
    simp [htbad]
  have hlin : t * R y - QuadraticMap.polar R w y ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    apply htbad
    calc
      t = (t * R y) * (R y)⁻¹ := by field_simp [hyq]
      _ = QuadraticMap.polar R w y * (R y)⁻¹ := by rw [h]
  let u := t • y
  let v := w - u
  have huq : R u ≠ 0 := by
    simp only [u, QuadraticMap.map_smul, smul_eq_mul]
    exact mul_ne_zero (mul_ne_zero ht0 ht0) hyq
  have hvq_formula : R v =
      t * (t * R y - QuadraticMap.polar R w y) := by
    simp only [v, sub_eq_add_neg, u, QuadraticMap.map_add R,
      QuadraticMap.map_neg, QuadraticMap.map_smul,
      QuadraticMap.polar_neg_right, QuadraticMap.polar_smul_right,
      hwq, zero_add, smul_eq_mul]
    ring
  refine ⟨u, v, ?_, huq, ?_⟩
  · simp [v]
  · rw [hvq_formula]
    exact mul_ne_zero ht0 hlin

private lemma eichlerTransform_factor
    {W : Type u} [AddCommGroup W] [Module k W]
    [Fintype k] [Fact (2 < Fintype.card k)] (R : QuadraticForm k W)
    (hpolar : Function.Injective R.polarBilin) (w : W) :
    ∃ as : List (AnisotropicVector (hyperbolicSumForm R)),
      ∀ x, symmetryProduct (hyperbolicSumForm R) as x =
        eichlerTransform R w x := by
  by_cases hw0 : w = 0
  · subst w
    refine ⟨[], ?_⟩
    intro x
    simp [symmetryProduct, eichlerTransform]
  by_cases hwq : R w = 0
  · obtain ⟨u, v, huv, huq, hvq⟩ :=
      isotropic_eq_add_anisotropic R hpolar w hw0 hwq
    obtain ⟨as, has⟩ := eichlerTransform_factor_of_anisotropic R u huq
    obtain ⟨bs, hbs⟩ := eichlerTransform_factor_of_anisotropic R v hvq
    refine ⟨as ++ bs, ?_⟩
    intro x
    rw [symmetryProduct_append, LinearEquiv.mul_apply, hbs, has,
      eichlerTransform_add, huv]
  · exact eichlerTransform_factor_of_anisotropic R w hwq

private noncomputable def liftTailSymmetry
    {W : Type u} [AddCommGroup W] [Module k W]
    (R : QuadraticForm k W) (a : AnisotropicVector R) :
    List (AnisotropicVector (hyperbolicSumForm R)) :=
  [⟨hyperbolicHead (k := k) (W := W) + hyperbolicPartner (k := k) (W := W), by
      simp [hyperbolicHead, hyperbolicPartner]⟩,
    ⟨hyperbolicHead (k := k) (W := W) - hyperbolicPartner (k := k) (W := W), by
      simp [hyperbolicHead, hyperbolicPartner]⟩,
    ⟨hyperbolicTail (k := k) (a : W), by
      simpa only [hyperbolicTail_form] using a.property⟩]

private lemma liftTailSymmetry_apply
    {W : Type u} [AddCommGroup W] [Module k W]
    (R : QuadraticForm k W) (a : AnisotropicVector R)
    (x : (k × k) × W) :
    symmetryProduct (hyperbolicSumForm R) (liftTailSymmetry R a) x =
      (x.1, conjugationSymmetry R (a : W) a.property x.2) := by
  rw [symmetryProduct_apply]
  simp only [liftTailSymmetry, List.foldr_cons, List.foldr_nil]
  rw [conjugationSymmetry_apply, conjugationSymmetry_apply,
    conjugationSymmetry_apply, conjugationSymmetry_apply]
  rcases x with ⟨⟨p, q⟩, x⟩
  apply Prod.ext
  · apply Prod.ext <;>
      simp [hyperbolicHead, hyperbolicPartner, hyperbolicTail]
  · simp [hyperbolicHead, hyperbolicPartner, hyperbolicTail]

private noncomputable def liftTailSymmetries
    {W : Type u} [AddCommGroup W] [Module k W]
    (R : QuadraticForm k W) (as : List (AnisotropicVector R)) :
    List (AnisotropicVector (hyperbolicSumForm R)) :=
  as.flatMap (liftTailSymmetry R)

private lemma liftTailSymmetries_apply
    {W : Type u} [AddCommGroup W] [Module k W]
    (R : QuadraticForm k W) (as : List (AnisotropicVector R))
    (x : (k × k) × W) :
    symmetryProduct (hyperbolicSumForm R) (liftTailSymmetries R as) x =
      (x.1, symmetryProduct R as x.2) := by
  induction as generalizing x with
  | nil => rfl
  | cons a as ih =>
      rw [show liftTailSymmetries R (a :: as) =
          liftTailSymmetry R a ++ liftTailSymmetries R as by
        simp [liftTailSymmetries]]
      rw [symmetryProduct_append, LinearEquiv.mul_apply, ih,
        liftTailSymmetry_apply]
      rfl

private noncomputable def symmetryProductIsometry (Q : QuadraticForm k V)
    (as : List (AnisotropicVector Q)) : Q.IsometryEquiv Q where
  toLinearEquiv := symmetryProduct Q as
  map_app' := symmetryProduct_preserves Q as

private noncomputable def isometryComp (Q : QuadraticForm k V)
    (f g : Q.IsometryEquiv Q) : Q.IsometryEquiv Q where
  toLinearEquiv := f.toLinearEquiv * g.toLinearEquiv
  map_app' x := by
    change Q (f (g x)) = Q x
    rw [f.map_app, g.map_app]

private lemma isometryComp_apply (Q : QuadraticForm k V)
    (f g : Q.IsometryEquiv Q) (x : V) :
    isometryComp Q f g x = f (g x) := rfl

private def tailRestrictionLinearMap
    {W : Type u} [AddCommGroup W] [Module k W]
    (g : ((k × k) × W) ≃ₗ[k] ((k × k) × W)) : W →ₗ[k] W where
  toFun w := (g (hyperbolicTail (k := k) w)).2
  map_add' u v := by
    rw [show hyperbolicTail (k := k) (u + v) =
        hyperbolicTail (k := k) u + hyperbolicTail (k := k) v by
      simp [hyperbolicTail]]
    rw [map_add]
    rfl
  map_smul' c w := by
    rw [show hyperbolicTail (k := k) (c • w) =
        c • hyperbolicTail (k := k) w by simp [hyperbolicTail]]
    rw [map_smul]
    rfl

private lemma isometry_fixes_plane_tail
    {W : Type u} [AddCommGroup W] [Module k W]
    (R : QuadraticForm k W) (g : (hyperbolicSumForm R).IsometryEquiv
      (hyperbolicSumForm R))
    (he : g (hyperbolicHead (k := k) (W := W)) =
      hyperbolicHead (k := k) (W := W))
    (hd : g (hyperbolicPartner (k := k) (W := W)) =
      hyperbolicPartner (k := k) (W := W)) (w : W) :
    g (hyperbolicTail (k := k) w) =
      hyperbolicTail (k := k) (tailRestrictionLinearMap g.toLinearEquiv w) := by
  let e := hyperbolicHead (k := k) (W := W)
  let d := hyperbolicPartner (k := k) (W := W)
  let z := hyperbolicTail (k := k) w
  have hez := isometry_polar g e z
  have hdz := isometry_polar g d z
  change g e = e at he
  change g d = d at hd
  rw [he] at hez
  rw [hd] at hdz
  apply Prod.ext
  · apply Prod.ext
    · simpa [e, d, z, hyperbolicHead, hyperbolicPartner, hyperbolicTail]
        using hdz
    · simpa [e, d, z, hyperbolicHead, hyperbolicPartner, hyperbolicTail]
        using hez
  · rfl

private def SymmetryGenerated (R : QuadraticForm k V) : Prop :=
  ∀ g : R.IsometryEquiv R,
    ∃ as : List (AnisotropicVector R),
      ∀ x, g x = symmetryProduct R as x

private lemma symmetryGenerated_hyperbolicSum
    {W : Type u} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] [Fintype k] [Fact (2 < Fintype.card k)]
    (R : QuadraticForm k W) (hpolar : Function.Injective R.polarBilin)
    (hgen : SymmetryGenerated R) :
    SymmetryGenerated (hyperbolicSumForm R) := by
  intro g
  let e := hyperbolicHead (k := k) (W := W)
  let d := hyperbolicPartner (k := k) (W := W)
  let u := g e
  have he0 : e ≠ 0 := by
    intro h
    have h' := congrArg (fun z : (k × k) × W => z.1.1) h
    simp [e, hyperbolicHead] at h'
  have hu0 : u ≠ 0 := by
    intro hu
    apply he0
    apply g.injective
    simpa [u] using hu
  have huq : hyperbolicSumForm R u = 0 := by
    rw [show hyperbolicSumForm R u = hyperbolicSumForm R e by
      simp [u, g.map_app]]
    exact hyperbolicHead_form R
  obtain ⟨ps, hps⟩ := move_isotropic_to_head R hpolar u huq hu0
  let pIso := symmetryProductIsometry (hyperbolicSumForm R) ps
  let g1 := isometryComp (hyperbolicSumForm R) pIso g
  have hg1e : g1 e = e := by
    change symmetryProduct (hyperbolicSumForm R) ps (g e) = e
    exact hps
  let x := g1 d
  let w := x.2
  have hxq : hyperbolicSumForm R x = 0 := by
    rw [show hyperbolicSumForm R x = hyperbolicSumForm R d by
      simp [x, g1.map_app]]
    exact hyperbolicPartner_form R
  have hxsecond : x.1.2 = 1 := by
    have h := isometry_polar g1 e d
    rw [hg1e] at h
    simpa [x, e, d, hyperbolicHead, hyperbolicPartner] using h
  have hxfirst : x.1.1 = -R w := by
    rw [hyperbolicSumForm_apply, hxsecond, mul_one] at hxq
    exact eq_neg_of_add_eq_zero_left hxq
  have hx : x = ((-R w, 1), w) := by
    apply Prod.ext
    · apply Prod.ext
      · exact hxfirst
      · exact hxsecond
    · rfl
  obtain ⟨ts, hts⟩ := eichlerTransform_factor R hpolar (-w)
  let tIso := symmetryProductIsometry (hyperbolicSumForm R) ts
  let g2 := isometryComp (hyperbolicSumForm R) tIso g1
  have hg2e : g2 e = e := by
    change symmetryProduct (hyperbolicSumForm R) ts (g1 e) = e
    rw [hg1e, hts, eichlerTransform_head]
  have hg2d : g2 d = d := by
    change symmetryProduct (hyperbolicSumForm R) ts (g1 d) = d
    rw [show g1 d = x from rfl, hx, hts, eichlerTransform_neg_partner]
  let hmap := tailRestrictionLinearMap g2.toLinearEquiv
  have hmap_injective : Function.Injective hmap := by
    intro v z hvz
    have hgv := isometry_fixes_plane_tail R g2 hg2e hg2d v
    have hgz := isometry_fixes_plane_tail R g2 hg2e hg2d z
    have hgz' : g2 (hyperbolicTail (k := k) v) =
        g2 (hyperbolicTail (k := k) z) := by
      rw [hgv, hgz, hvz]
    have hvz' := g2.injective hgz'
    exact congrArg Prod.snd hvz'
  have hmap_surjective : Function.Surjective hmap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := hmap) rfl).mp
      hmap_injective
  let hle : W ≃ₗ[k] W := LinearEquiv.ofBijective hmap
    ⟨hmap_injective, hmap_surjective⟩
  let hIso : R.IsometryEquiv R :=
    { toLinearEquiv := hle
      map_app' := by
        intro v
        change R (hmap v) = R v
        have hq := g2.map_app (hyperbolicTail (k := k) v)
        rw [isometry_fixes_plane_tail R g2 hg2e hg2d] at hq
        simpa only [hyperbolicTail_form] using hq }
  obtain ⟨cs, hcs⟩ := hgen hIso
  let ls := liftTailSymmetries R cs
  have hg2block (z : (k × k) × W) :
      g2 z = (z.1, hIso z.2) := by
    have hsecond : (g2 z).1.2 = z.1.2 := by
      have h := isometry_polar g2 e z
      rw [hg2e] at h
      simpa [e, hyperbolicHead] using h
    have hfirst : (g2 z).1.1 = z.1.1 := by
      have h := isometry_polar g2 d z
      rw [hg2d] at h
      simpa [d, hyperbolicPartner] using h
    have hzdecomp : z = z.1.1 • e + z.1.2 • d +
        hyperbolicTail (k := k) z.2 := by
      ext <;> simp [e, d, hyperbolicHead, hyperbolicPartner, hyperbolicTail]
    have htail : (g2 z).2 = hIso z.2 := by
      change (g2 z).2 = (g2 (hyperbolicTail (k := k) z.2)).2
      conv_lhs => rw [hzdecomp]
      rw [map_add, map_add, map_smul, map_smul, hg2e, hg2d]
      simp [e, d, hyperbolicHead, hyperbolicPartner]
    apply Prod.ext
    · apply Prod.ext <;> assumption
    · exact htail
  have hg2factor (z : (k × k) × W) :
      g2 z = symmetryProduct (hyperbolicSumForm R) ls z := by
    rw [hg2block, liftTailSymmetries_apply]
    apply Prod.ext
    · rfl
    · exact hcs z.2
  refine ⟨ps.reverse ++ ts.reverse ++ ls, ?_⟩
  intro z
  rw [symmetryProduct_append, symmetryProduct_append,
    LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  rw [← hg2factor]
  change g z = symmetryProduct (hyperbolicSumForm R) ps.reverse
    (symmetryProduct (hyperbolicSumForm R) ts.reverse
      (symmetryProduct (hyperbolicSumForm R) ts
        (symmetryProduct (hyperbolicSumForm R) ps (g z))))
  rw [symmetryProduct_reverse_left, symmetryProduct_reverse_left]

private noncomputable def isometrySymm
    {W : Type u} [AddCommGroup W] [Module k W]
    {Q : QuadraticForm k V} {R : QuadraticForm k W}
    (e : Q.IsometryEquiv R) : R.IsometryEquiv Q where
  toLinearEquiv := e.toLinearEquiv.symm
  map_app' x := by
    simp

private lemma isometry_polar_between
    {W : Type u} [AddCommGroup W] [Module k W]
    {Q : QuadraticForm k V} {R : QuadraticForm k W}
    (e : Q.IsometryEquiv R) (x y : V) :
    QuadraticMap.polar R (e x) (e y) = QuadraticMap.polar Q x y := by
  simp only [QuadraticMap.polar, ← map_add, e.map_app]

private noncomputable def pullbackAnisotropic
    {W : Type u} [AddCommGroup W] [Module k W]
    {Q : QuadraticForm k V} {R : QuadraticForm k W}
    (e : Q.IsometryEquiv R) (a : AnisotropicVector R) :
    AnisotropicVector Q :=
  ⟨e.toLinearEquiv.symm (a : W), by
    have h := (isometrySymm e).map_app (a : W)
    exact h ▸ a.property⟩

private lemma conjugationSymmetry_pullback
    {W : Type u} [AddCommGroup W] [Module k W]
    {Q : QuadraticForm k V} {R : QuadraticForm k W}
    (e : Q.IsometryEquiv R) (a : AnisotropicVector R) (x : V) :
    e (conjugationSymmetry Q (pullbackAnisotropic e a : V)
        (pullbackAnisotropic e a).property x) =
      conjugationSymmetry R (a : W) a.property (e x) := by
  rw [conjugationSymmetry_apply, conjugationSymmetry_apply]
  have hq : Q (e.toLinearEquiv.symm (a : W)) = R a :=
    (isometrySymm e).map_app (a : W)
  have hp : QuadraticMap.polar Q (e.toLinearEquiv.symm (a : W)) x =
      QuadraticMap.polar R (a : W) (e x) := by
    symm
    simpa [pullbackAnisotropic] using
      isometry_polar_between e (e.toLinearEquiv.symm (a : W)) x
  change e (((Q (e.toLinearEquiv.symm (a : W)))⁻¹ *
      QuadraticMap.polar Q (e.toLinearEquiv.symm (a : W)) x) •
      e.toLinearEquiv.symm (a : W) - x) = _
  rw [map_sub, map_smul]
  have hea : e (e.toLinearEquiv.symm (a : W)) = (a : W) :=
    e.toLinearEquiv.apply_symm_apply (a : W)
  rw [hea, hq, hp]

private lemma pullback_symmetryProduct
    {W : Type u} [AddCommGroup W] [Module k W]
    {Q : QuadraticForm k V} {R : QuadraticForm k W}
    (e : Q.IsometryEquiv R) (as : List (AnisotropicVector R)) (x : V) :
    e (symmetryProduct Q (as.map (pullbackAnisotropic e)) x) =
      symmetryProduct R as (e x) := by
  induction as generalizing x with
  | nil => rfl
  | cons a as ih =>
      change e (conjugationSymmetry Q (pullbackAnisotropic e a : V)
          (pullbackAnisotropic e a).property
          (symmetryProduct Q (List.map (pullbackAnisotropic e) as) x)) = _
      rw [conjugationSymmetry_pullback, ih]
      rfl

private lemma symmetryGenerated_of_isometry
    {W : Type u} [AddCommGroup W] [Module k W]
    {Q : QuadraticForm k V} {R : QuadraticForm k W}
    (e : Q.IsometryEquiv R) (hgen : SymmetryGenerated R) :
    SymmetryGenerated Q := by
  intro g
  let hle : W ≃ₗ[k] W :=
    e.toLinearEquiv.symm.trans (g.toLinearEquiv.trans e.toLinearEquiv)
  let hIso : R.IsometryEquiv R :=
    { toLinearEquiv := hle
      map_app' := by
        intro y
        dsimp only [hle]
        change R (e (g (e.toLinearEquiv.symm y))) = R y
        rw [e.map_app, g.map_app]
        simp }
  obtain ⟨as, has⟩ := hgen hIso
  refine ⟨as.map (pullbackAnisotropic e), ?_⟩
  intro x
  apply e.injective
  change e (g x) = e (symmetryProduct Q (as.map (pullbackAnisotropic e)) x)
  rw [pullback_symmetryProduct]
  have hh := has (e x)
  change e (g (e.toLinearEquiv.symm (e x))) =
    symmetryProduct R as (e x) at hh
  have hex : e.toLinearEquiv.symm (e x) = x :=
    e.toLinearEquiv.symm_apply_apply x
  rw [hex] at hh
  exact hh

private noncomputable def hyperbolicConsLinearEquiv (n : Nat) :
    ((k × k) × HyperbolicSpace k n) ≃ₗ[k] HyperbolicSpace k (n + 1) where
  toFun z := (Fin.cons z.1.1 z.2.1, Fin.cons z.1.2 z.2.2)
  invFun z := ((z.1 0, z.2 0),
    (fun i => z.1 i.succ, fun i => z.2 i.succ))
  left_inv z := by
    apply Prod.ext
    · apply Prod.ext <;> rfl
    · apply Prod.ext <;> funext i <;> rfl
  right_inv z := by
    apply Prod.ext <;> funext i
    · refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    · refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  map_add' z w := by
    apply Prod.ext <;> funext i
    · refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    · refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  map_smul' c z := by
    apply Prod.ext <;> funext i
    · refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    · refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private noncomputable def hyperbolicConsIsometry (n : Nat) :
    (hyperbolicSumForm (hyperbolicForm (k := k) n)).IsometryEquiv
      (hyperbolicForm (k := k) (n + 1)) where
  toLinearEquiv := hyperbolicConsLinearEquiv n
  map_app' z := by
    rw [hyperbolicForm_apply, Fin.sum_univ_succ]
    change z.1.1 * z.1.2 + (∑ i, z.2.1 i * z.2.2 i) =
      z.1.1 * z.1.2 + hyperbolicForm (k := k) n z.2
    rw [hyperbolicForm_apply]

private lemma hyperbolicPolar_injective' (n : Nat) :
    Function.Injective (hyperbolicForm (k := k) n).polarBilin := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  apply Prod.ext <;> funext i
  · have hi := congrArg (fun f => f (0, Pi.single i 1)) hv
    rw [hyperbolicForm_polar] at hi
    simpa [Pi.single_apply] using hi
  · have hi := congrArg (fun f => f (Pi.single i 1, 0)) hv
    rw [hyperbolicForm_polar] at hi
    simpa [Pi.single_apply] using hi

private lemma hyperbolic_symmetryGenerated [Fintype k] [Fact (2 < Fintype.card k)] (n : Nat) :
    SymmetryGenerated (hyperbolicForm (k := k) n) := by
  induction n with
  | zero =>
      intro g
      refine ⟨[], ?_⟩
      intro x
      exact Subsingleton.elim _ _
  | succ n ih =>
      have hsum : SymmetryGenerated
          (hyperbolicSumForm (hyperbolicForm (k := k) n)) :=
        symmetryGenerated_hyperbolicSum (hyperbolicForm (k := k) n)
          (hyperbolicPolar_injective' n) ih
      exact symmetryGenerated_of_isometry
        (isometrySymm (hyperbolicConsIsometry (k := k) n)) hsum

/-- Ordered anisotropic symmetry factorization of a hyperbolic isometry over
any finite field with more than two elements. -/
public theorem hyperbolic_factorization [Fintype k] (hcard : 2 < Fintype.card k)
    (n : ℕ) (g : (hyperbolicForm (k := k) n).IsometryEquiv (hyperbolicForm n)) :
    ∃ as : List {v : HyperbolicSpace k n // hyperbolicForm n v ≠ 0},
      ∀ v, g v = as.foldr
        (fun (a : {v : HyperbolicSpace k n // hyperbolicForm n v ≠ 0}) w => ((hyperbolicForm n a)⁻¹ *
          QuadraticMap.polar (hyperbolicForm n) a w) • (a : HyperbolicSpace k n) - w) v := by
  let : Fact (2 < Fintype.card k) := ⟨hcard⟩
  obtain ⟨as, has⟩ := hyperbolic_symmetryGenerated n g
  refine ⟨as, ?_⟩
  intro v
  rw [has, symmetryProduct_apply]
  clear has g
  induction as generalizing v with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldr_cons]
      rw [conjugationSymmetry_apply, ih]

end Theory.AlgebraicGroup.FiniteSymmetryFactorization
