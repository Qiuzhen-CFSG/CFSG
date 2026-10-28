module
public import Theory.GroupAction.SymplecticRankThree.Homotheties
public import Mathlib.RingTheory.LittleWedderburn

/-!
# The scalar field reconstructed from incidence

The regular abelian translation group supplies additive axis subgroups.
Their direction-preserving additive endomorphisms form a ring. A scalar
vanishing on a nonzero vector vanishes off its axis by intersecting two
other directions, and then vanishes on the axis by addition. Thus the ring
has no zero divisors. The finite-domain form of Wedderburn's theorem gives
all field laws, with multiplication literally composition of endomorphisms.

Spatial homotheties act on translations by conjugation. Evaluation therefore
identifies the scalar field with each affine axis, proving its order is q,
not merely a divisor of q. No multiplication, distributivity, coordinate map
or recognition theorem is assumed. All constructions include q=2.

Source: the coordinatization step in Higman (1964), Lemma 10, pp.153–154.
FieldPlane applies this field to actual line equations and source coordinates.
-/

public noncomputable section
open scoped IsMulCommutative
namespace Theory.GroupAction.SymplecticRankThree.AffineFrame
variable {Ω : Type*} [Finite Ω] {q : ℕ} {D : PolarityDesign Ω q}
variable (f : AffineFrame D)
variable (hl : ∀ a b, a ≠ b → (D.line a b).ncard = q+1) (hq : 2 ≤ q)
local instance : AddCommGroup (f.Base hl hq) := f.affineAddCommGroup hl hq

@[expose] def translationAddEquiv : Additive (f.translations hl hq) ≃+ f.Base hl hq where
  toEquiv := Additive.toMul.trans (f.translationEquiv hl hq)
  map_add' T U := f.translationEquiv_mul hl hq T.toMul U.toMul

/-- The additive subgroup belonging to an actual direction. -/
@[expose] def axisGroup (d : f.Direction hl hq) : AddSubgroup (f.Base hl hq) :=
  (f.directionTranslations hl hq d).toAddSubgroup.map (f.translationAddEquiv hl hq).toAddMonoidHom

theorem mem_axisGroup (d : f.Direction hl hq) (x : f.Base hl hq) :
    x ∈ f.axisGroup hl hq d ↔ (x : Ω) ∈ D.line d f.origin := by
  constructor
  · rintro ⟨T,hT,rfl⟩
    exact (f.translation_direction_iff hl hq T.toMul d).mp hT
  · intro hx
    let T := (f.translationEquiv hl hq).symm x
    refine ⟨Additive.ofMul T,?_,(f.translationEquiv hl hq).apply_symm_apply x⟩
    apply (f.translation_direction_iff hl hq T d).mpr
    simpa only [T,Equiv.apply_symm_apply] using hx

theorem axisGroup_card (d : f.Direction hl hq) : Nat.card (f.axisGroup hl hq d) = q := by
  change Nat.card ((f.directionTranslations hl hq d).toAddSubgroup.map
    (f.translationAddEquiv hl hq).toAddMonoidHom) = q
  rw [Nat.card_congr (AddSubgroup.equivMapOfInjective _ (f.translationAddEquiv hl hq).toAddMonoidHom
    (f.translationAddEquiv hl hq).injective).symm.toEquiv]
  exact f.directionTranslations_card hl hq d

theorem exists_axisGroup (x : f.Base hl hq) : ∃ d, x ∈ f.axisGroup hl hq d := by
  obtain ⟨d,hd⟩ := ((f.translationEquiv hl hq).symm x).val.translation_spec.mp
    ((f.translationEquiv hl hq).symm x).property
  refine ⟨d,(f.mem_axisGroup hl hq d x).mpr ?_⟩
  have hh := (f.translation_direction_iff hl hq ((f.translationEquiv hl hq).symm x) d).mp hd
  simpa only [Equiv.apply_symm_apply] using hh

theorem axisGroup_inter {d e : f.Direction hl hq} (hde : d ≠ e)
    {x : f.Base hl hq} (hd : x ∈ f.axisGroup hl hq d) (he : x ∈ f.axisGroup hl hq e) : x = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  exact direction_lines_unique (fun hh => hde (Subtype.ext hh)) f.origin_not_mem f.origin_not_mem
    ((f.mem_axisGroup hl hq d x).mp hd) ((f.mem_axisGroup hl hq e x).mp he)
    (D.right_mem_line _ _) (D.right_mem_line _ _)

theorem exists_not_mem_axisGroup (d : f.Direction hl hq) :
    ∃ x : f.Base hl hq, x ∉ f.axisGroup hl hq d := by
  obtain ⟨x,hx⟩ := f.exists_base_off_line hl hq d f.origin
    (f.direction_ne_affine hl hq d f.originPoint)
  exact ⟨x,fun hh => hx ((f.mem_axisGroup hl hq d x).mp hh)⟩

/-- Scalars are additive endomorphisms preserving every geometric direction. -/
@[expose] def scalarRing : Subring (AddMonoid.End (f.Base hl hq)) where
  carrier := {φ | ∀ d, ∀ x ∈ f.axisGroup hl hq d, φ x ∈ f.axisGroup hl hq d}
  zero_mem' := fun d _ _ => (f.axisGroup hl hq d).zero_mem
  one_mem' := fun _ _ hx => hx
  add_mem' hφ hψ := fun d x hx => (f.axisGroup hl hq d).add_mem (hφ d x hx) (hψ d x hx)
  neg_mem' hφ := fun d x hx => (f.axisGroup hl hq d).neg_mem (hφ d x hx)
  mul_mem' hφ hψ := fun d x hx => hφ d _ (hψ d x hx)

namespace Scalar
variable {f hl hq}

/-- A scalar vanishing at a nonzero point vanishes everywhere. This uses
all direction subgroups, rather than an assumed division property. -/
theorem eq_zero_of_apply_eq_zero (φ : f.scalarRing hl hq) {a : f.Base hl hq}
    (ha : a ≠ 0) (hφa : φ.val a = 0) : φ = 0 := by
  obtain ⟨d,hd⟩ := f.exists_axisGroup hl hq a
  have outside (x : f.Base hl hq) (hx : x ∉ f.axisGroup hl hq d) : φ.val x = 0 := by
    obtain ⟨e,he⟩ := f.exists_axisGroup hl hq x
    obtain ⟨t,ht⟩ := f.exists_axisGroup hl hq (x+a)
    have hed : e ≠ d := fun hh => hx (hh ▸ he)
    have het : e ≠ t := by
      intro hh
      have ht' : x+a ∈ f.axisGroup hl hq e := by rw [hh]; exact ht
      have hat : a ∈ f.axisGroup hl hq e := by
        simpa only [add_sub_cancel_left] using (f.axisGroup hl hq e).sub_mem ht' he
      exact ha (f.axisGroup_inter hl hq hed hat hd)
    apply f.axisGroup_inter hl hq het (φ.property e x he)
    have hh := φ.property t (x+a) ht
    simpa only [map_add,hφa,add_zero] using hh
  obtain ⟨b,hb⟩ := f.exists_not_mem_axisGroup hl hq d
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro x
  change φ.val x = 0
  by_cases hx : x ∈ f.axisGroup hl hq d
  · have hxb : x+b ∉ f.axisGroup hl hq d := by
      intro hh
      exact hb (by simpa only [add_sub_cancel_left,add_sub_cancel_right] using (f.axisGroup hl hq d).sub_mem hh hx)
    have hh := outside (x+b) hxb
    simpa only [map_add,outside b hb,add_zero] using hh
  · exact outside x hx

theorem injective {φ : f.scalarRing hl hq} (hφ : φ ≠ 0) : Function.Injective φ.val := by
  intro a b hab
  by_contra hh
  exact hφ (eq_zero_of_apply_eq_zero φ (sub_ne_zero.mpr hh) (by rw [map_sub,hab,sub_self]))

theorem evaluation_injective {a : f.Base hl hq} (ha : a ≠ 0) :
    Function.Injective (fun φ : f.scalarRing hl hq => φ.val a) := by
  intro φ ψ he
  apply sub_eq_zero.mp
  apply eq_zero_of_apply_eq_zero (φ-ψ) ha
  change φ.val a - ψ.val a = 0
  exact sub_eq_zero.mpr he

end Scalar

instance scalarRing_nontrivial : Nontrivial (f.scalarRing hl hq) := by
  obtain ⟨a,ha⟩ := f.exists_not_mem_axisGroup hl hq (f.directionI hl hq)
  have ha0 : a ≠ 0 := fun hh => ha (hh ▸ (f.axisGroup hl hq _).zero_mem)
  refine ⟨⟨0,1,?_⟩⟩
  intro hh
  exact ha0 (congrArg (fun φ : f.scalarRing hl hq => φ.val a) hh).symm

instance scalarRing_noZeroDivisors : NoZeroDivisors (f.scalarRing hl hq) where
  eq_zero_or_eq_zero_of_mul_eq_zero {φ ψ} hh := by
    by_cases hφ : φ = 0
    · exact Or.inl hφ
    right
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro x
    change ψ.val x = 0
    apply Scalar.injective hφ
    have he := congrArg (fun ξ : f.scalarRing hl hq => ξ.val x) hh
    change φ.val (ψ.val x) = 0 at he
    exact he.trans (map_zero φ.val).symm

instance scalarRing_finite : Finite (f.scalarRing hl hq) :=
  Finite.of_injective (fun φ : f.scalarRing hl hq => (φ.val : f.Base hl hq → f.Base hl hq))
    (fun _ _ he => Subtype.ext (AddMonoidHom.ext (congrFun he)))

instance scalarRing_isDomain : IsDomain (f.scalarRing hl hq) :=
  (isDomain_iff_noZeroDivisors_and_nontrivial _).mpr ⟨inferInstance,inferInstance⟩

/-- The direction-preserving endomorphism ring is a finite field. Its order
still needs the spatial homothety construction. -/
@[expose, instance_reducible] def scalarField : Field (f.scalarRing hl hq) :=
  (Finite.isDomain_to_isField (f.scalarRing hl hq)).toField

end Theory.GroupAction.SymplecticRankThree.AffineFrame

namespace Theory.GroupAction.SymplecticRankThree.AffineFrame
variable {Ω : Type*} [Finite Ω] {q : ℕ} {D : PolarityDesign Ω q}
variable (f : AffineFrame D)
variable (hl : ∀ a b, a ≠ b → (D.line a b).ncard = q+1) (hq : 2 ≤ q)
local instance : AddCommGroup (f.Base hl hq) := f.affineAddCommGroup hl hq

namespace Motion
variable {f hl hq} (E : f.Motion hl hq)

/-- The actual geometric motion fixing the origin is a scalar of the
constructed field, by conjugation on the translation group. -/
@[expose] def toScalar : f.scalarRing hl hq :=
  ⟨((f.translationAddEquiv hl hq).symm.trans
    (E.conjugateTranslations.toAdditive.trans (f.translationAddEquiv hl hq))).toAddMonoidHom,by
    intro d x hx
    obtain ⟨T,hT,rfl⟩ := hx
    refine ⟨_,E.conjugateTranslations_direction T.toMul d hT,?_⟩
    change _ = (f.translationAddEquiv hl hq)
      (E.conjugateTranslations.toAdditive
        ((f.translationAddEquiv hl hq).symm ((f.translationAddEquiv hl hq) T)))
    rw [AddEquiv.symm_apply_apply]
    rfl⟩

theorem toScalar_apply (hE : E.affineEquiv (f.baseOrigin hl hq) = f.baseOrigin hl hq)
    (x : f.Base hl hq) : E.toScalar.val x = E.affineEquiv x := by
  change f.translationEquiv hl hq (E.conjugateTranslations ((f.translationEquiv hl hq).symm x)) = _
  have hh := E.conjugateTranslations_evaluation hE ((f.translationEquiv hl hq).symm x)
  simpa only [Equiv.apply_symm_apply] using hh

end Motion

/-- The geometric dilations make evaluation onto an entire nonzero axis
surjective; the scalar field cannot be a proper subfield of the needed size. -/
theorem scalar_evaluation_bijective (d : f.Direction hl hq) (a : f.axisGroup hl hq d)
    (ha : a.val ≠ 0) :
    Function.Bijective (fun φ : f.scalarRing hl hq =>
      (⟨φ.val a,φ.property d a a.property⟩ : f.axisGroup hl hq d)) := by
  constructor
  · intro φ ψ he
    exact Scalar.evaluation_injective ha (congrArg Subtype.val he)
  · intro b
    by_cases hb : b.val = 0
    · exact ⟨0,Subtype.ext hb.symm⟩
    have hao : (a.val : Ω) ≠ f.origin := fun hh => ha (Subtype.ext (Subtype.ext hh))
    have hbo : (b.val : Ω) ≠ f.origin := fun hh => hb (Subtype.ext (Subtype.ext hh))
    have haL := (f.mem_axisGroup hl hq d a.val).mp a.property
    have hbL := (f.mem_axisGroup hl hq d b.val).mp b.property
    have hL : D.line f.origin (a.val : Ω) = D.line d f.origin :=
      D.line_eq_of_mem_of_mem (f.direction_ne_affine hl hq d f.originPoint)
        (D.right_mem_line _ _) haL hao.symm
    obtain ⟨E,hE,hEa⟩ := f.exists_homothety hl hq a.val b.val hao hbo (hL.symm ▸ hbL)
    exact ⟨E.toScalar,Subtype.ext ((E.toScalar_apply hE a).trans hEa)⟩

theorem exists_axisGroup_nonzero (d : f.Direction hl hq) :
    ∃ a : f.axisGroup hl hq d, a.val ≠ 0 := by
  let : Fintype (f.axisGroup hl hq d) := Fintype.ofFinite _
  have hc : 1 < Fintype.card (f.axisGroup hl hq d) := by
    rw [← Nat.card_eq_fintype_card,f.axisGroup_card hl hq d]
    omega
  let : Nontrivial (f.axisGroup hl hq d) := Fintype.one_lt_card_iff_nontrivial.mp hc
  obtain ⟨a,ha⟩ := exists_ne (0 : f.axisGroup hl hq d)
  exact ⟨a,fun hh => ha (Subtype.ext hh)⟩

/-- The field constructed from actual incidence has exactly q elements. -/
theorem scalarField_card : Nat.card (f.scalarRing hl hq) = q := by
  obtain ⟨a,ha⟩ := f.exists_axisGroup_nonzero hl hq (f.directionI hl hq)
  rw [Nat.card_congr (Equiv.ofBijective _ (f.scalar_evaluation_bijective hl hq _ a ha))]
  exact f.axisGroup_card hl hq _

end Theory.GroupAction.SymplecticRankThree.AffineFrame
