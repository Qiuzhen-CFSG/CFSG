module
public import Theory.GroupAction.SymplecticRankThree.ScalarField
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Field-linear coordinates on the actual affine plane

Evaluation of the reconstructed scalar field makes the affine plane a vector
space. Each actual direction is one-dimensional. Nonzero vectors on the two
coordinate axes form a basis: distinct direction subgroups meet only at zero,
and their q² linear combinations exhaust the plane. This gives an equivalence
with the field squared and proves every actual line is a scalar affine span.

Finite-field uniqueness transports the coordinates to any supplied field of
order q. Every line then has the ordinary equation x=c or y=mx+b. The field
laws and order are proved in ScalarField; neither an affine-linearity premise
nor a coordinatization callback is assumed. The construction includes q=2.
Extending this plane chart to projective three-space remains a further step.

Source: the expanded coordinatization in Higman (1964), Lemma 10,
pp.153–154. SourceField and FieldChapter12 apply these equations to the
literal original-source parabolic cosets and selected C₂ row.
-/

public noncomputable section
namespace Theory.GroupAction.SymplecticRankThree.AffineFrame
variable {Ω : Type*} [Finite Ω] {q : ℕ} {D : PolarityDesign Ω q}
variable (f : AffineFrame D)
variable (hl : ∀ a b, a ≠ b → (D.line a b).ncard = q+1) (hq : 2 ≤ q)
local instance : AddCommGroup (f.Base hl hq) := f.affineAddCommGroup hl hq
local instance : Field (f.scalarRing hl hq) := f.scalarField hl hq

/-- Evaluation is the scalar action on the actual affine plane. -/
@[expose, instance_reducible] def scalarModule : Module (f.scalarRing hl hq) (f.Base hl hq) :=
  Module.compHom (f.Base hl hq) (f.scalarRing hl hq).subtype

local instance : Module (f.scalarRing hl hq) (f.Base hl hq) := f.scalarModule hl hq

theorem scalar_smul_apply (r : f.scalarRing hl hq) (x : f.Base hl hq) : r • x = r.val x := rfl

/-- Every direction is a one-dimensional space over the constructed field. -/
theorem mem_axisGroup_iff_smul (d : f.Direction hl hq) {a : f.Base hl hq}
    (ha : a ∈ f.axisGroup hl hq d) (ha0 : a ≠ 0) (x : f.Base hl hq) :
    x ∈ f.axisGroup hl hq d ↔ ∃ r : f.scalarRing hl hq, x = r • a := by
  constructor
  · intro hx
    obtain ⟨r,hr⟩ := (f.scalar_evaluation_bijective hl hq d ⟨a,ha⟩ ha0).2 ⟨x,hx⟩
    exact ⟨r,(congrArg Subtype.val hr).symm⟩
  · rintro ⟨r,rfl⟩
    exact r.property d a ha

/-- All actual affine lines have the ordinary field-linear equation. -/
theorem affine_line_scalar (a b x : f.Base hl hq) :
    (x : Ω) ∈ D.line a b ↔ ∃ r : f.scalarRing hl hq, x = a + r • (b-a) := by
  by_cases hab : a = b
  · subst b
    simp only [D.line_eq_singleton hq,Set.mem_singleton_iff,sub_self,smul_zero,add_zero,
      exists_const]
    exact ⟨fun hh => Subtype.ext (Subtype.ext hh),fun hh => congrArg (fun y : f.Base hl hq => (y : Ω)) hh⟩
  have hba : b-a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  obtain ⟨d,hd⟩ := f.exists_axisGroup hl hq (b-a)
  have hbL : (b : Ω) ∈ D.line d a := (f.affine_line_add hl hq b a d).mpr
    ((f.mem_axisGroup hl hq d (b-a)).mp hd)
  have hab' : (a : Ω) ≠ b := fun hh => hab (Subtype.ext (Subtype.ext hh))
  have hL : D.line a b = D.line d a := D.line_eq_of_mem_of_mem
    (f.direction_ne_affine hl hq d a.val) (D.right_mem_line _ _) hbL hab'
  rw [hL,f.affine_line_add hl hq x a d,← f.mem_axisGroup hl hq d (x-a),
    f.mem_axisGroup_iff_smul hl hq d hd hba]
  constructor
  · rintro ⟨r,hr⟩
    exact ⟨r,by rw [← hr]; abel⟩
  · rintro ⟨r,rfl⟩
    exact ⟨r,by abel⟩

@[expose] def axisUnit (d : f.Direction hl hq) : f.axisGroup hl hq d :=
  (f.exists_axisGroup_nonzero hl hq d).choose

theorem axisUnit_ne_zero (d : f.Direction hl hq) : (f.axisUnit hl hq d).val ≠ 0 :=
  (f.exists_axisGroup_nonzero hl hq d).choose_spec

@[expose] def planeLinearMap : (f.scalarRing hl hq × f.scalarRing hl hq) →ₗ[f.scalarRing hl hq] f.Base hl hq where
  toFun z := z.1 • (f.axisUnit hl hq (f.directionI hl hq)).val +
    z.2 • (f.axisUnit hl hq (f.directionJ hl hq)).val
  map_add' z w := by simp only [Prod.fst_add,Prod.snd_add,add_smul]; abel
  map_smul' r z := by simp only [smul_add,smul_smul]; rfl

theorem planeLinearMap_bijective : Function.Bijective (f.planeLinearMap hl hq) := by
  have hker (z : f.scalarRing hl hq × f.scalarRing hl hq)
      (hz : f.planeLinearMap hl hq z = 0) : z = 0 := by
    let u := f.axisUnit hl hq (f.directionI hl hq)
    let v := f.axisUnit hl hq (f.directionJ hl hq)
    change z.1 • u.val + z.2 • v.val = 0 at hz
    have hu : z.1 • u.val = 0 := by
      apply f.axisGroup_inter hl hq (d := f.directionI hl hq) (e := f.directionJ hl hq)
        (fun he => f.ij_ne (congrArg Subtype.val he))
      · exact z.1.property _ u.val u.property
      · rw [eq_neg_of_add_eq_zero_left hz]
        exact (f.axisGroup hl hq _).neg_mem (z.2.property _ v.val v.property)
    have hv : z.2 • v.val = 0 := by simpa only [hu,zero_add] using hz
    exact Prod.ext ((smul_eq_zero.mp hu).resolve_right (f.axisUnit_ne_zero hl hq _))
      ((smul_eq_zero.mp hv).resolve_right (f.axisUnit_ne_zero hl hq _))
  have hinj : Function.Injective (f.planeLinearMap hl hq) := by
    intro z w he
    apply sub_eq_zero.mp
    exact hker (z-w) (by rw [map_sub,he,sub_self])
  let : Fintype (f.scalarRing hl hq × f.scalarRing hl hq) := Fintype.ofFinite _
  let : Fintype (f.Base hl hq) := Fintype.ofFinite _
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨hinj,?_⟩
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,Nat.card_prod,
    f.scalarField_card hl hq,Nat.card_congr (f.baseEquiv hl hq),Nat.card_prod,
    (f.axes_card hl hq).1,(f.axes_card hl hq).2.1]

/-- Field-linear coordinates on the actual affine plane. -/
@[expose] def fieldPlaneCoordinates :
    f.Base hl hq ≃ₗ[f.scalarRing hl hq] f.scalarRing hl hq × f.scalarRing hl hq :=
  (LinearEquiv.ofBijective (f.planeLinearMap hl hq) (f.planeLinearMap_bijective hl hq)).symm

theorem fieldPlaneCoordinates_line (a b x : f.Base hl hq) :
    (x : Ω) ∈ D.line a b ↔ ∃ r : f.scalarRing hl hq,
      f.fieldPlaneCoordinates hl hq x = f.fieldPlaneCoordinates hl hq a +
        r • (f.fieldPlaneCoordinates hl hq b - f.fieldPlaneCoordinates hl hq a) := by
  rw [f.affine_line_scalar hl hq]
  apply exists_congr
  intro r
  rw [← map_sub,← map_smul,← map_add]
  exact (f.fieldPlaneCoordinates hl hq).injective.eq_iff.symm

end Theory.GroupAction.SymplecticRankThree.AffineFrame

namespace Theory.GroupAction.SymplecticRankThree.AffineFrame
variable {Ω : Type*} [Finite Ω] {q : ℕ} {D : PolarityDesign Ω q}
variable (f : AffineFrame D)
variable (hl : ∀ a b, a ≠ b → (D.line a b).ncard = q+1) (hq : 2 ≤ q)
local instance : AddCommGroup (f.Base hl hq) := f.affineAddCommGroup hl hq
local instance : Field (f.scalarRing hl hq) := f.scalarField hl hq
local instance : Module (f.scalarRing hl hq) (f.Base hl hq) := f.scalarModule hl hq
variable (F : Type*) [Field F] [Finite F] (hcard : q = Nat.card F)

/-- Identify the constructed field with any given finite field of the same
order. This is uniqueness of finite fields, after field laws and cardinality
have been proved from the actual geometry. -/
@[expose] def scalarFieldEquiv : f.scalarRing hl hq ≃+* F := by
  let : Fintype (f.scalarRing hl hq) := Fintype.ofFinite _
  let : Fintype F := Fintype.ofFinite _
  exact FiniteField.ringEquivOfCardEq
    (by simpa only [← Nat.card_eq_fintype_card,f.scalarField_card hl hq] using hcard)

@[expose] def fieldPlaneCoordinatesOver : f.Base hl hq ≃ F × F :=
  (f.fieldPlaneCoordinates hl hq).toEquiv.trans
    ((f.scalarFieldEquiv hl hq F hcard).toEquiv.prodCongr (f.scalarFieldEquiv hl hq F hcard).toEquiv)

theorem fieldPlaneCoordinatesOver_line (a b x : f.Base hl hq) :
    (x : Ω) ∈ D.line a b ↔ ∃ r : F,
      f.fieldPlaneCoordinatesOver hl hq F hcard x = f.fieldPlaneCoordinatesOver hl hq F hcard a +
        r • (f.fieldPlaneCoordinatesOver hl hq F hcard b - f.fieldPlaneCoordinatesOver hl hq F hcard a) := by
  let e := f.scalarFieldEquiv hl hq F hcard
  let c := f.fieldPlaneCoordinates hl hq
  have hm (r : f.scalarRing hl hq) (u v : f.Base hl hq) :
      f.fieldPlaneCoordinatesOver hl hq F hcard (u+r•v) =
        f.fieldPlaneCoordinatesOver hl hq F hcard u + e r • f.fieldPlaneCoordinatesOver hl hq F hcard v := by
    change (e (c (u+r•v)).1,e (c (u+r•v)).2) = _
    rw [map_add,map_smul]
    apply Prod.ext
    · change e ((c u).1 + r*(c v).1) = e (c u).1 + e r*e (c v).1
      rw [map_add,map_mul]
    · change e ((c u).2 + r*(c v).2) = e (c u).2 + e r*e (c v).2
      rw [map_add,map_mul]
  have hs (u v : f.Base hl hq) :
      f.fieldPlaneCoordinatesOver hl hq F hcard (u-v) =
        f.fieldPlaneCoordinatesOver hl hq F hcard u - f.fieldPlaneCoordinatesOver hl hq F hcard v := by
    change (e (c (u-v)).1,e (c (u-v)).2) = _
    rw [map_sub]
    apply Prod.ext <;> simp only [Prod.fst_sub,Prod.snd_sub,map_sub] <;> rfl
  rw [f.affine_line_scalar hl hq]
  constructor
  · rintro ⟨r,rfl⟩
    exact ⟨e r,by rw [hm,hs]⟩
  · rintro ⟨r,hr⟩
    refine ⟨e.symm r,(f.fieldPlaneCoordinatesOver hl hq F hcard).injective ?_⟩
    rw [hm,hs,e.apply_symm_apply]
    exact hr

end Theory.GroupAction.SymplecticRankThree.AffineFrame

namespace Theory.GroupAction.SymplecticRankThree.AffineFrame
variable {Ω : Type*} [Finite Ω] {q : ℕ} {D : PolarityDesign Ω q}
variable (f : AffineFrame D)
variable (hl : ∀ a b, a ≠ b → (D.line a b).ncard = q+1) (hq : 2 ≤ q)
variable (F : Type*) [Field F] [Finite F] (hcard : q = Nat.card F)

/-- Exhaustive ordinary field equations for every actual affine line. -/
theorem fieldPlaneCoordinatesOver_equations (a b : f.Base hl hq) (hab : a ≠ b) :
    (∃ c : F, ∀ x : f.Base hl hq, (x : Ω) ∈ D.line a b ↔
      (f.fieldPlaneCoordinatesOver hl hq F hcard x).1 = c) ∨
    (∃ m c : F, ∀ x : f.Base hl hq, (x : Ω) ∈ D.line a b ↔
      (f.fieldPlaneCoordinatesOver hl hq F hcard x).2 =
        m * (f.fieldPlaneCoordinatesOver hl hq F hcard x).1+c) := by
  let C := f.fieldPlaneCoordinatesOver hl hq F hcard
  let A := C a
  let B := C b
  have hAB : A ≠ B := fun hh => hab (C.injective hh)
  by_cases hv : A.1 = B.1
  · left
    have hy : B.2-A.2 ≠ 0 := by
      intro hh
      exact hAB (Prod.ext hv (sub_eq_zero.mp hh).symm)
    refine ⟨A.1,?_⟩
    intro x
    rw [f.fieldPlaneCoordinatesOver_line hl hq F hcard]
    change (∃ r : F, C x = A+r•(B-A)) ↔ (C x).1 = A.1
    constructor
    · rintro ⟨r,hr⟩
      have hh := congrArg Prod.fst hr
      change (C x).1 = A.1 + r*(B.1-A.1) at hh
      simpa only [← hv,sub_self,mul_zero,add_zero] using hh
    · intro hx
      refine ⟨((C x).2-A.2)/(B.2-A.2),Prod.ext ?_ ?_⟩
      · change (C x).1 = A.1 + _ * (B.1-A.1)
        rw [← hv,sub_self,mul_zero,add_zero]
        exact hx
      · change (C x).2 = A.2 + ((C x).2-A.2)/(B.2-A.2)*(B.2-A.2)
        rw [div_mul_cancel₀ _ hy]
        ring
  · right
    have hx : B.1-A.1 ≠ 0 := fun hh => hv (sub_eq_zero.mp hh).symm
    refine ⟨(B.2-A.2)/(B.1-A.1),A.2-(B.2-A.2)/(B.1-A.1)*A.1,?_⟩
    intro x
    rw [f.fieldPlaneCoordinatesOver_line hl hq F hcard]
    change (∃ r : F, C x = A+r•(B-A)) ↔
      (C x).2 = (B.2-A.2)/(B.1-A.1)*(C x).1 + (A.2-(B.2-A.2)/(B.1-A.1)*A.1)
    constructor
    · rintro ⟨r,hr⟩
      rw [hr]
      change A.2+r*(B.2-A.2) = (B.2-A.2)/(B.1-A.1)*(A.1+r*(B.1-A.1)) +
        (A.2-(B.2-A.2)/(B.1-A.1)*A.1)
      field_simp
      ring
    · intro he
      refine ⟨((C x).1-A.1)/(B.1-A.1),Prod.ext ?_ ?_⟩
      · change (C x).1 = A.1 + ((C x).1-A.1)/(B.1-A.1)*(B.1-A.1)
        rw [div_mul_cancel₀ _ hx]
        ring
      · change (C x).2 = A.2 + ((C x).1-A.1)/(B.1-A.1)*(B.2-A.2)
        rw [he]
        ring

end Theory.GroupAction.SymplecticRankThree.AffineFrame
