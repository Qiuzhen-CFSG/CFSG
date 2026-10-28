module
public import Theory.GroupAction.SymplecticRankThree.FieldPlane
public import Mathlib.LinearAlgebra.Projectivization.Collinear

/-!
# Completing the reconstructed affine plane

Adjoin the actual points at infinity to the affine vector plane constructed
from geometric translations. A finite point x has homogeneous vector (1,x);
a direction has vector (0,u), with u a nonzero vector of its actual axis.
Direction subgroups meet only at zero, so these vectors give distinct
projective points; their scalar-span description proves surjectivity.

Every finite line is the span of its affine point and direction vector.
The infinite line is the span of the two chosen axis vectors. Uniqueness of
a two-dimensional span then proves preservation of all lines in both
directions, including coincident endpoints. This completes a whole source
plane, including q=2, without assuming projective coordinates.

Source: the expanded coordinatization step of Higman, *Finite permutation
groups of rank 3* (1964), Lemma 10, pp.153–154. ProjectivePlanes transports
the coordinates to the original field and every polar block; extension to
one projective three-space chart remains a further obligation.
-/

public noncomputable section
open Projectivization
namespace Theory.GroupAction.SymplecticRankThree.AffineFrame
variable {Ω : Type*} [Finite Ω] {q : ℕ} {D : PolarityDesign Ω q}
variable (f : AffineFrame D)
variable (hl : ∀ a b, a ≠ b → (D.line a b).ncard = q+1) (hq : 2 ≤ q)
local instance : DecidablePred (· ∈ D.block f.infinity) := Classical.decPred _
local instance : AddCommGroup (f.Base hl hq) := f.affineAddCommGroup hl hq
local instance : Field (f.scalarRing hl hq) := f.scalarField hl hq
local instance : Module (f.scalarRing hl hq) (f.Base hl hq) := f.scalarModule hl hq

private theorem zero_scalar_smul (a : f.Base hl hq) :
    (0 : f.scalarRing hl hq) • a = 0 := rfl

@[expose] def planeVector (x : f.Plane hl hq) : f.scalarRing hl hq × f.Base hl hq :=
  if hx : (x : Ω) ∈ D.block f.infinity then (0,(f.axisUnit hl hq ⟨x,hx,x.property⟩).val)
    else (1,⟨⟨x,hx⟩,x.property⟩)

theorem planeVector_affine (a : f.Base hl hq) :
    f.planeVector hl hq ⟨a,a.property⟩ = (1,a) := by
  simp only [planeVector,dif_neg a.val.property]

theorem planeVector_direction (d : f.Direction hl hq) :
    f.planeVector hl hq ⟨d,d.property.2⟩ = (0,(f.axisUnit hl hq d).val) := by
  simp only [planeVector,dif_pos d.property.1]

theorem planeVector_ne_zero (x : f.Plane hl hq) : f.planeVector hl hq x ≠ 0 := by
  by_cases hx : (x : Ω) ∈ D.block f.infinity
  · let d : f.Direction hl hq := ⟨x,hx,x.property⟩
    rw [show x = (⟨d,d.property.2⟩ : f.Plane hl hq) from rfl,f.planeVector_direction]
    exact fun he => f.axisUnit_ne_zero hl hq d (congrArg Prod.snd he)
  · let a : f.Base hl hq := ⟨⟨x,hx⟩,x.property⟩
    rw [show x = (⟨a,a.property⟩ : f.Plane hl hq) from rfl,f.planeVector_affine]
    exact fun he => one_ne_zero (congrArg Prod.fst he)

@[expose] def planeProjective (x : f.Plane hl hq) :
    Projectivization (f.scalarRing hl hq) (f.scalarRing hl hq × f.Base hl hq) :=
  Projectivization.mk _ (f.planeVector hl hq x) (f.planeVector_ne_zero hl hq x)

theorem planeProjective_eq_iff (x y : f.Plane hl hq) :
    f.planeProjective hl hq x = f.planeProjective hl hq y ↔
      ∃ r : f.scalarRing hl hq, r • f.planeVector hl hq y = f.planeVector hl hq x :=
  mk_eq_mk_iff' _ _ _ _ _

theorem planeProjective_injective : Function.Injective (f.planeProjective hl hq) := by
  intro x y he
  obtain ⟨r,hr⟩ := (f.planeProjective_eq_iff hl hq x y).mp he
  by_cases hx : (x : Ω) ∈ D.block f.infinity
  · let d : f.Direction hl hq := ⟨x,hx,x.property⟩
    have hd : f.planeVector hl hq x = (0,(f.axisUnit hl hq d).val) := f.planeVector_direction hl hq d
    by_cases hy : (y : Ω) ∈ D.block f.infinity
    · let e : f.Direction hl hq := ⟨y,hy,y.property⟩
      have he' : f.planeVector hl hq y = (0,(f.axisUnit hl hq e).val) := f.planeVector_direction hl hq e
      rw [hd,he'] at hr
      by_contra hxy
      have hde : d ≠ e := fun hh => hxy (Subtype.ext (congrArg (fun t : f.Direction hl hq => (t : Ω)) hh))
      apply f.axisUnit_ne_zero hl hq d
      apply f.axisGroup_inter hl hq hde (f.axisUnit hl hq d).property
      rw [← show r • (f.axisUnit hl hq e).val = (f.axisUnit hl hq d).val from congrArg Prod.snd hr]
      exact r.property e _ (f.axisUnit hl hq e).property
    · let a : f.Base hl hq := ⟨⟨y,hy⟩,y.property⟩
      rw [hd,show f.planeVector hl hq y = (1,a) from f.planeVector_affine hl hq a] at hr
      have hr0 : r = 0 := by have hh := congrArg Prod.fst hr; change r*1 = _ at hh; simpa only [mul_one] using hh
      have hh := congrArg Prod.snd hr
      change r.val a = (f.axisUnit hl hq d).val at hh
      rw [hr0] at hh
      exact (f.axisUnit_ne_zero hl hq d hh.symm).elim
  · let a : f.Base hl hq := ⟨⟨x,hx⟩,x.property⟩
    have ha : f.planeVector hl hq x = (1,a) := f.planeVector_affine hl hq a
    by_cases hy : (y : Ω) ∈ D.block f.infinity
    · let e : f.Direction hl hq := ⟨y,hy,y.property⟩
      rw [ha,show f.planeVector hl hq y = (0,(f.axisUnit hl hq e).val) from f.planeVector_direction hl hq e] at hr
      have hh := congrArg Prod.fst hr
      change r*0 = 1 at hh
      exact (zero_ne_one (by simpa only [mul_zero] using hh)).elim
    · let b : f.Base hl hq := ⟨⟨y,hy⟩,y.property⟩
      rw [ha,show f.planeVector hl hq y = (1,b) from f.planeVector_affine hl hq b] at hr
      have hr1 : r = 1 := by have hh := congrArg Prod.fst hr; change r*1 = _ at hh; simpa only [mul_one] using hh
      have hba : b = a := by have hh := congrArg Prod.snd hr; change r • b = a at hh; simpa only [hr1,one_smul] using hh
      exact Subtype.ext (congrArg (fun t : f.Base hl hq => (t : Ω)) hba.symm)

theorem planeProjective_surjective : Function.Surjective (f.planeProjective hl hq) := by
  intro p
  induction p using Projectivization.ind with | h v hv =>
  by_cases hc : v.1 = 0
  · have hv2 : v.2 ≠ 0 := fun hh => hv (Prod.ext hc hh)
    obtain ⟨d,hd⟩ := f.exists_axisGroup hl hq v.2
    obtain ⟨r,hr⟩ := (f.mem_axisGroup_iff_smul hl hq d (f.axisUnit hl hq d).property
      (f.axisUnit_ne_zero hl hq d) v.2).mp hd
    refine ⟨⟨d,d.property.2⟩,?_⟩
    symm
    apply (mk_eq_mk_iff' _ _ _ _ _).mpr
    refine ⟨r,?_⟩
    rw [f.planeVector_direction]
    exact Prod.ext (by change r*0 = v.1; rw [mul_zero,hc]) hr.symm
  · let a : f.Base hl hq := v.1⁻¹ • v.2
    refine ⟨⟨a,a.property⟩,?_⟩
    symm
    apply (mk_eq_mk_iff' _ _ _ _ _).mpr
    refine ⟨v.1,?_⟩
    rw [f.planeVector_affine]
    exact Prod.ext (mul_one _) (by change v.1 • (v.1⁻¹ • v.2) = v.2; rw [smul_smul,mul_inv_cancel₀ hc,one_smul])

@[expose] def projectivePlaneCoordinates : f.Plane hl hq ≃
    Projectivization (f.scalarRing hl hq) (f.scalarRing hl hq × f.Base hl hq) :=
  Equiv.ofBijective (f.planeProjective hl hq)
    ⟨f.planeProjective_injective hl hq,f.planeProjective_surjective hl hq⟩


/-- Membership in a homogeneous line is membership of its displayed vector
in the span of the two displayed endpoint vectors. -/
theorem planeProjective_le_iff (a b x : f.Plane hl hq) :
    (f.planeProjective hl hq x).submodule ≤
      (f.planeProjective hl hq a).submodule ⊔ (f.planeProjective hl hq b).submodule ↔
    f.planeVector hl hq x ∈ Submodule.span (f.scalarRing hl hq)
      {f.planeVector hl hq a,f.planeVector hl hq b} := by
  simp only [planeProjective,submodule_mk,← Submodule.span_insert,
    Submodule.span_singleton_le_iff_mem]

theorem planeVector_span_finrank (a b : f.Plane hl hq) (hab : a ≠ b) :
    Module.finrank (f.scalarRing hl hq) (Submodule.span (f.scalarRing hl hq)
      {f.planeVector hl hq a,f.planeVector hl hq b}) = 2 := by
  have hh := (f.planeProjective_injective hl hq).ne hab
  change Projectivization.mk _ _ _ ≠ Projectivization.mk _ _ _ at hh
  rw [← independent_pair_iff_ne,independent_mk_iff_LinearIndependent] at hh
  rw [← Matrix.range_cons_cons_empty _ _ ![]]
  simpa only [Fintype.card_fin] using finrank_span_eq_card hh

/-- A finite line with its actual point at infinity is a homogeneous
vector line, with no new incidence assumption. -/
theorem planeVector_mem_direction_span (d : f.Direction hl hq) (a : f.Base hl hq)
    (x : f.Plane hl hq) :
    f.planeVector hl hq x ∈ Submodule.span (f.scalarRing hl hq)
      {f.planeVector hl hq ⟨d,d.property.2⟩,f.planeVector hl hq ⟨a,a.property⟩} ↔
      (x : Ω) ∈ D.line d a := by
  rw [f.planeVector_direction,f.planeVector_affine,Submodule.mem_span_pair]
  by_cases hx : (x : Ω) ∈ D.block f.infinity
  · let e : f.Direction hl hq := ⟨x,hx,x.property⟩
    rw [show f.planeVector hl hq x = (0,(f.axisUnit hl hq e).val) from f.planeVector_direction hl hq e]
    have hxline : (x : Ω) ∈ D.line d a ↔ e = d := by
      constructor
      · intro hh
        exact Subtype.ext ((D.infinity_on_line d.property.1 a.val.property hh).mp hx)
      · intro hh
        have he : (x : Ω) = d := congrArg Subtype.val hh
        rw [he]
        exact D.left_mem_line _ _
    rw [hxline]
    constructor
    · rintro ⟨r,s,hrs⟩
      have hs : s = 0 := by
        have hh := congrArg Prod.fst hrs
        change r*0+s*1 = 0 at hh
        simpa only [mul_zero,mul_one,zero_add] using hh
      have he : r • (f.axisUnit hl hq d).val = (f.axisUnit hl hq e).val := by
        have hh := congrArg Prod.snd hrs
        change r • (f.axisUnit hl hq d).val + s • a = _ at hh
        simpa only [hs,f.zero_scalar_smul hl hq,add_zero] using hh
      by_contra hed
      apply f.axisUnit_ne_zero hl hq e
      apply f.axisGroup_inter hl hq hed (f.axisUnit hl hq e).property
      rw [← he]
      exact r.property d _ (f.axisUnit hl hq d).property
    · intro hed
      rw [hed]
      exact ⟨1,0,Prod.ext (by simp) (by change 1 • _ + (0 : f.scalarRing hl hq) • a = _; rw [one_smul,f.zero_scalar_smul,add_zero])⟩
  · let b : f.Base hl hq := ⟨⟨x,hx⟩,x.property⟩
    rw [show f.planeVector hl hq x = (1,b) from f.planeVector_affine hl hq b]
    change (∃ r s : f.scalarRing hl hq,
      r • (0,(f.axisUnit hl hq d).val) + s • (1,a) = (1,b)) ↔ (b : Ω) ∈ D.line d a
    rw [f.affine_line_add hl hq b a d,← f.mem_axisGroup hl hq d (b-a),
      f.mem_axisGroup_iff_smul hl hq d (f.axisUnit hl hq d).property
        (f.axisUnit_ne_zero hl hq d)]
    constructor
    · rintro ⟨r,s,hrs⟩
      have hs : s = 1 := by
        have hh := congrArg Prod.fst hrs
        change r*0+s*1 = 1 at hh
        simpa only [mul_zero,mul_one,zero_add] using hh
      have he : r • (f.axisUnit hl hq d).val + a = b := by
        have hh := congrArg Prod.snd hrs
        change r • (f.axisUnit hl hq d).val + s • a = b at hh
        simpa only [hs,one_smul] using hh
      exact ⟨r,by rw [← he]; abel⟩
    · rintro ⟨r,hr⟩
      refine ⟨r,1,Prod.ext (by simp) ?_⟩
      change r • (f.axisUnit hl hq d).val + 1 • a = b
      rw [one_smul,← hr,sub_add_cancel]

/-- The entire line at infinity, not just its two chosen axis directions,
is the zero-first-coordinate projective line. -/
theorem planeVector_mem_infinity_span (x : f.Plane hl hq) :
    f.planeVector hl hq x ∈ Submodule.span (f.scalarRing hl hq)
      {f.planeVector hl hq ⟨f.i,(f.level_spec hl hq f.originPoint).1⟩,
       f.planeVector hl hq ⟨f.j,(f.level_spec hl hq f.originPoint).2.1⟩} ↔
      (x : Ω) ∈ D.block f.infinity := by
  rw [show f.planeVector hl hq ⟨f.i,(f.level_spec hl hq f.originPoint).1⟩ =
      (0,(f.axisUnit hl hq (f.directionI hl hq)).val) from f.planeVector_direction hl hq (f.directionI hl hq),
    show f.planeVector hl hq ⟨f.j,(f.level_spec hl hq f.originPoint).2.1⟩ =
      (0,(f.axisUnit hl hq (f.directionJ hl hq)).val) from f.planeVector_direction hl hq (f.directionJ hl hq),
    Submodule.mem_span_pair]
  by_cases hx : (x : Ω) ∈ D.block f.infinity
  · let d : f.Direction hl hq := ⟨x,hx,x.property⟩
    rw [show f.planeVector hl hq x = (0,(f.axisUnit hl hq d).val) from f.planeVector_direction hl hq d]
    refine ⟨fun _ => hx,fun _ => ?_⟩
    obtain ⟨z,hz⟩ := (f.planeLinearMap_bijective hl hq).2 (f.axisUnit hl hq d).val
    exact ⟨z.1,z.2,Prod.ext (by simp) hz⟩
  · let a : f.Base hl hq := ⟨⟨x,hx⟩,x.property⟩
    rw [show f.planeVector hl hq x = (1,a) from f.planeVector_affine hl hq a]
    refine ⟨?_,fun hh => (hx hh).elim⟩
    rintro ⟨r,s,hrs⟩
    have hh := congrArg Prod.fst hrs
    change r*0+s*0 = 1 at hh
    exact (zero_ne_one (by simpa only [mul_zero,add_zero] using hh)).elim

/-- Every original plane line is the inverse image of a vector subspace
of dimension two under the constructed homogeneous coordinates. -/
theorem exists_plane_line_subspace (a b : f.Plane hl hq) (hab : a ≠ b) :
    ∃ W : Submodule (f.scalarRing hl hq) (f.scalarRing hl hq × f.Base hl hq),
      Module.finrank (f.scalarRing hl hq) W = 2 ∧
      ∀ x : f.Plane hl hq, f.planeVector hl hq x ∈ W ↔ (x : Ω) ∈ D.line a b := by
  have hab' : (a : Ω) ≠ b := fun hh => hab (Subtype.ext hh)
  have finite_case (a b : f.Plane hl hq) (hab : (a : Ω) ≠ b)
      (ha : (a : Ω) ∉ D.block f.infinity) :
      ∃ W : Submodule (f.scalarRing hl hq) (f.scalarRing hl hq × f.Base hl hq),
        Module.finrank (f.scalarRing hl hq) W = 2 ∧
        ∀ x : f.Plane hl hq, f.planeVector hl hq x ∈ W ↔ (x : Ω) ∈ D.line a b := by
    obtain ⟨d,hdL,hdInf⟩ := D.line_meets_block hl (by omega) hab f.infinity
    have hdp := D.line_subset_block a.property b.property hdL
    let d' : f.Direction hl hq := ⟨d,hdInf,hdp⟩
    let a' : f.Base hl hq := ⟨⟨a,ha⟩,a.property⟩
    have hda : d ≠ (a : Ω) := fun he => ha (he ▸ hdInf)
    have hL : D.line d a = D.line a b := D.line_eq_of_mem_of_mem hab hdL (D.left_mem_line _ _) hda
    refine ⟨Submodule.span _ {f.planeVector hl hq ⟨d,hdp⟩,f.planeVector hl hq a},
      f.planeVector_span_finrank hl hq _ _ (fun he => hda (congrArg Subtype.val he)),?_⟩
    intro x
    exact (f.planeVector_mem_direction_span hl hq d' a' x).trans (by rw [hL])
  by_cases ha : (a : Ω) ∈ D.block f.infinity
  · by_cases hb : (b : Ω) ∈ D.block f.infinity
    · have hp : f.level hl hq f.originPoint ≠ f.infinity := by
        intro he
        exact f.origin_not_mem (he ▸ (f.level_spec hl hq f.originPoint).2.2)
      have hL := D.intersection_eq_line hl hp ⟨a.property,ha⟩ ⟨b.property,hb⟩ hab'
      refine ⟨Submodule.span _
        {f.planeVector hl hq ⟨f.i,(f.level_spec hl hq f.originPoint).1⟩,
         f.planeVector hl hq ⟨f.j,(f.level_spec hl hq f.originPoint).2.1⟩},
        f.planeVector_span_finrank hl hq _ _ (fun he => f.ij_ne (congrArg Subtype.val he)),?_⟩
      intro x
      rw [f.planeVector_mem_infinity_span,← hL]
      exact ⟨fun hx => ⟨x.property,hx⟩,fun hx => hx.2⟩
    · obtain ⟨W,hW,hWx⟩ := finite_case b a hab'.symm hb
      exact ⟨W,hW,fun x => (hWx x).trans (by rw [D.line_comm])⟩
  · exact finite_case a b hab' ha

/-- The completed projective plane coordinates preserve every line in
both directions, including the line at infinity and coincident endpoints. -/
theorem projectivePlaneCoordinates_line (a b x : f.Plane hl hq) :
    (f.projectivePlaneCoordinates hl hq x).submodule ≤
      (f.projectivePlaneCoordinates hl hq a).submodule ⊔
        (f.projectivePlaneCoordinates hl hq b).submodule ↔ (x : Ω) ∈ D.line a b := by
  change (f.planeProjective hl hq x).submodule ≤
    (f.planeProjective hl hq a).submodule ⊔ (f.planeProjective hl hq b).submodule ↔ _
  rw [f.planeProjective_le_iff]
  by_cases hab : a = b
  · subst b
    rw [show ({f.planeVector hl hq a,f.planeVector hl hq a} : Set _) = {f.planeVector hl hq a} by ext; simp,
      Submodule.mem_span_singleton,← f.planeProjective_eq_iff]
    rw [(f.planeProjective_injective hl hq).eq_iff,D.line_eq_singleton hq,Set.mem_singleton_iff]
    exact ⟨fun he => congrArg Subtype.val he,fun he => Subtype.ext he⟩
  · obtain ⟨W,hW,hWx⟩ := f.exists_plane_line_subspace hl hq a b hab
    have hle : Submodule.span (f.scalarRing hl hq)
        {f.planeVector hl hq a,f.planeVector hl hq b} ≤ W := by
      apply Submodule.span_le.mpr
      intro v hv
      rcases hv with rfl | rfl
      · exact (hWx a).mpr (D.left_mem_line _ _)
      · exact (hWx b).mpr (D.right_mem_line _ _)
    have : Module.Finite (f.scalarRing hl hq) W := Module.finite_of_finrank_eq_succ hW
    rw [Submodule.eq_of_le_of_finrank_eq hle ((f.planeVector_span_finrank hl hq a b hab).trans hW.symm)]
    exact hWx x


end Theory.GroupAction.SymplecticRankThree.AffineFrame
