module
public import Theory.GroupAction.SymplecticRankThree.FieldSpace
public import Mathlib.LinearAlgebra.Projectivization.Independence

/-!
# Completing spatial affine coordinates to projective coordinates

A normalized affine chart preserving every line determines each actual point
at infinity by its nonzero axis vector. For a field with a scalar different
from zero and one, planes through the origin become vector subspaces: addition
is expressed by two affine combinations. Coplanar line intersection then proves
the common direction formula for every parallel affine line and the span formula
for lines at infinity. Homogenization is bijective and preserves every source
line in both directions.

The input affine chart is constructed in FieldSpace. ProjectiveCoordinates
instantiates it and transports the result to the original finite field; the
independent binary recognition handles the field of order two without this
nonbinary affine-combination step.

Source: Higman (1964), Lemma 10, pp.153–154, expanded projective
coordinatization after reconstruction of the incidence geometry.
-/

public noncomputable section
open Projectivization
namespace Theory.GroupAction.SymplecticRankThree.AffineFrame
variable {Ω : Type*} [Finite Ω] {q : ℕ} {D : PolarityDesign Ω q}
variable (f : AffineFrame D)
variable (hl : ∀ a b, a ≠ b → (D.line a b).ncard = q+1) (hq : 2 ≤ q)
variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V]

/-- An affine chart preserving the actual lines, normalized at the origin. -/
structure FieldChart where
  coords : f.Affine ≃ V
  origin_zero : coords f.originPoint = 0
  line_iff : ∀ a b x : f.Affine, (x : Ω) ∈ D.line a b ↔
    ∃ r : K, coords x = coords a + r • (coords b-coords a)

namespace FieldChart
variable {f K V} (C : FieldChart f K V)

@[simp] theorem coords_symm_zero : C.coords.symm 0 = f.originPoint :=
  C.coords.injective (by rw [Equiv.apply_symm_apply,C.origin_zero])

include hl hq in
theorem direction_point_exists (d : ↥(D.block f.infinity)) :
    ∃ a : f.AxisAt d, C.coords a.val ≠ 0 := by
  let o : f.AxisAt d := ⟨f.originPoint,D.right_mem_line _ _⟩
  have hc : 1 < Nat.card (f.AxisAt d) := by rw [f.axisAt_card hl d d.property]; omega
  let : Fintype (f.AxisAt d) := Fintype.ofFinite _
  let : Nontrivial (f.AxisAt d) := Fintype.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  obtain ⟨a,ha⟩ := exists_ne o
  exact ⟨a,fun he => ha (Subtype.ext (C.coords.injective (he.trans C.origin_zero.symm)))⟩

@[expose] def directionPoint (d : ↥(D.block f.infinity)) : f.AxisAt d :=
  (C.direction_point_exists hl hq d).choose

theorem directionPoint_ne (d : ↥(D.block f.infinity)) :
    (C.directionPoint hl hq d).val ≠ f.originPoint :=
  fun he => (C.direction_point_exists hl hq d).choose_spec (by
    change C.coords (C.directionPoint hl hq d).val = 0
    rw [he,C.origin_zero])

@[expose] def directionVector (d : ↥(D.block f.infinity)) : V :=
  C.coords (C.directionPoint hl hq d).val

theorem directionVector_ne_zero (d : ↥(D.block f.infinity)) : C.directionVector hl hq d ≠ 0 := by
  intro hh
  exact C.directionPoint_ne hl hq d (C.coords.injective (hh.trans C.origin_zero.symm))

theorem axis_line (d : ↥(D.block f.infinity)) (x : f.Affine) :
    (x : Ω) ∈ D.line d f.origin ↔ ∃ r : K, C.coords x = r • C.directionVector hl hq d := by
  let a := C.directionPoint hl hq d
  have hdo : (d : Ω) ≠ f.origin := fun he => f.origin_not_mem (he ▸ d.property)
  have hoa : f.origin ≠ (a : Ω) := fun he =>
    C.directionPoint_ne hl hq d (Subtype.ext he.symm)
  have hL : D.line f.origin (a : Ω) = D.line d f.origin :=
    D.line_eq_of_mem_of_mem hdo (D.right_mem_line _ _) a.property hoa
  have hh := C.line_iff f.originPoint a.val x
  simp only [C.origin_zero,sub_zero,zero_add] at hh
  exact (by rw [← hL]; exact hh)

theorem direction_eq_of_smul (d e : ↥(D.block f.infinity)) (r : K)
    (h : C.directionVector hl hq e = r • C.directionVector hl hq d) : e = d := by
  let a := C.directionPoint hl hq e
  have had : (a : Ω) ∈ D.line d f.origin := (C.axis_line hl hq d a.val).mpr ⟨r,h⟩
  have hoe : (e : Ω) ≠ f.origin := fun he => f.origin_not_mem (he ▸ e.property)
  have hod : (d : Ω) ≠ f.origin := fun he => f.origin_not_mem (he ▸ d.property)
  have hoa : f.origin ≠ (a : Ω) := fun he =>
    C.directionPoint_ne hl hq e (Subtype.ext he.symm)
  have heL : D.line f.origin (a : Ω) = D.line e f.origin :=
    D.line_eq_of_mem_of_mem hoe (D.right_mem_line _ _) a.property hoa
  have hdL : D.line f.origin (a : Ω) = D.line d f.origin :=
    D.line_eq_of_mem_of_mem hod (D.right_mem_line _ _) had hoa
  apply Subtype.ext
  exact (D.infinity_on_line d.property f.origin_not_mem
    (hdL ▸ heL.symm ▸ D.left_mem_line _ _)).mp e.property

variable (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
include t ht0 ht1

/-- A source plane through the origin becomes a vector subspace. The two
nonzero coefficients t and 1-t express addition by affine line operations. -/
@[expose] def planeSubmodule (p : Ω) (hp : f.origin ∈ D.block p) : Submodule K V where
  carrier := {v | (C.coords.symm v : Ω) ∈ D.block p}
  zero_mem' := by
    change (C.coords.symm 0 : Ω) ∈ D.block p
    rw [C.coords_symm_zero]
    exact hp
  smul_mem' r v hv := by
    apply D.line_subset_block hp hv
    apply (C.line_iff f.originPoint (C.coords.symm v) (C.coords.symm (r • v))).mpr
    exact ⟨r,by rw [C.origin_zero,Equiv.apply_symm_apply,Equiv.apply_symm_apply,sub_zero,zero_add]⟩
  add_mem' {u v} hu hv := by
    have hsmul (r : K) {w : V} (hw : (C.coords.symm w : Ω) ∈ D.block p) :
        (C.coords.symm (r • w) : Ω) ∈ D.block p := by
      apply D.line_subset_block hp hw
      apply (C.line_iff f.originPoint (C.coords.symm w) (C.coords.symm (r • w))).mpr
      exact ⟨r,by rw [C.origin_zero,Equiv.apply_symm_apply,Equiv.apply_symm_apply,sub_zero,zero_add]⟩
    have ht : 1-t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
    apply D.line_subset_block (hsmul ((1-t)⁻¹) hu) (hsmul (t⁻¹) hv)
    apply (C.line_iff (C.coords.symm ((1-t)⁻¹ • u)) (C.coords.symm (t⁻¹ • v))
      (C.coords.symm (u+v))).mpr
    refine ⟨t,?_⟩
    simp only [Equiv.apply_symm_apply]
    calc
      u+v = (1-t) • ((1-t)⁻¹ • u) + t • (t⁻¹ • v) := by
        rw [smul_smul,smul_smul,mul_inv_cancel₀ ht,mul_inv_cancel₀ ht0,one_smul,one_smul]
      _ = (1-t)⁻¹ • u + t • (t⁻¹ • v - (1-t)⁻¹ • u) := by
        rw [sub_smul,one_smul,smul_sub]
        abel

theorem directionVector_mem_planeSubmodule (p : Ω) (hp : f.origin ∈ D.block p)
    (d : ↥(D.block f.infinity)) :
    C.directionVector hl hq d ∈ C.planeSubmodule t ht0 ht1 p hp ↔ (d : Ω) ∈ D.block p := by
  change (C.coords.symm (C.coords (C.directionPoint hl hq d).val) : Ω) ∈ D.block p ↔ _
  rw [Equiv.symm_apply_apply]
  constructor
  · intro ha
    have hdo : (d : Ω) ≠ f.origin := fun he => f.origin_not_mem (he ▸ d.property)
    have hoa : f.origin ≠ (C.directionPoint hl hq d : Ω) := fun he =>
      C.directionPoint_ne hl hq d (Subtype.ext he.symm)
    have hL := D.line_eq_of_mem_of_mem hdo (D.right_mem_line _ _)
      (C.directionPoint hl hq d).property hoa
    exact D.line_subset_block hp ha (hL.symm ▸ D.left_mem_line _ _)
  · intro hd
    exact D.line_subset_block hd hp (C.directionPoint hl hq d).property

/-- The vector of an infinite point is the direction of every one of its
parallel affine lines, not just the line through the chosen origin. -/
theorem parallel_line (d : ↥(D.block f.infinity)) (a x : f.Affine) :
    (x : Ω) ∈ D.line d a ↔ ∃ r : K,
      C.coords x = C.coords a + r • C.directionVector hl hq d := by
  obtain ⟨p,hdp,hop,hap⟩ := D.exists_block_of_three hl (by omega) d f.origin a
  let W := C.planeSubmodule t ht0 ht1 p hop
  let v := C.directionVector hl hq d
  have hv : v ∈ W := (C.directionVector_mem_planeSubmodule hl hq t ht0 ht1 p hop d).mpr hdp
  have ha : C.coords a ∈ W := by
    change (C.coords.symm (C.coords a) : Ω) ∈ D.block p
    rw [Equiv.symm_apply_apply]
    exact hap
  let b := C.coords.symm (C.coords a+v)
  have hbp : (b : Ω) ∈ D.block p := W.add_mem ha hv
  have hb : C.coords b = C.coords a+v := C.coords.apply_symm_apply _
  have hab : (a : Ω) ≠ b := by
    intro he
    have hh : a = b := Subtype.ext he
    have hv0 : v = 0 := add_left_cancel (hb.symm.trans (by rw [← hh,add_zero]))
    exact C.directionVector_ne_zero hl hq d hv0
  have hdo : (d : Ω) ≠ f.origin := fun he => f.origin_not_mem (he ▸ d.property)
  have hda : (d : Ω) ≠ a := fun he => a.property (he ▸ d.property)
  obtain ⟨y,hyab,hydo⟩ := D.coplanar_lines_meet hl hab hdo hap hbp hdp hop
  have hdab : (d : Ω) ∈ D.line a b := by
    by_cases hy : y ∈ D.block f.infinity
    · have hyd := (D.infinity_on_line d.property f.origin_not_mem hydo).mp hy
      exact hyd ▸ hyab
    · let y' : f.Affine := ⟨y,hy⟩
      obtain ⟨r,hr⟩ := (C.line_iff a b y').mp hyab
      obtain ⟨s,hs⟩ := (C.axis_line hl hq d y').mp hydo
      rw [hb,add_sub_cancel_left] at hr
      have ha' : C.coords a = (s-r) • v := by rw [sub_smul,← hs,hr]; abel
      have hb' : C.coords b = (s-r+1) • v := by rw [hb,ha',add_smul,one_smul]
      have hal := (C.axis_line hl hq d a).mpr ⟨s-r,ha'⟩
      have hbl := (C.axis_line hl hq d b).mpr ⟨s-r+1,hb'⟩
      have he := D.line_eq_of_mem_of_mem hdo hal hbl hab
      exact he.symm ▸ D.left_mem_line _ _
  have hL : D.line d a = D.line a b :=
    D.line_eq_of_mem_of_mem hab hdab (D.left_mem_line _ _) hda
  rw [hL,C.line_iff]
  simp only [hb,add_sub_cancel_left]
  rfl

/-- Coordinates of all affine points of a plane through two independent
infinite directions lie in the span of those directions. -/
theorem planeSubmodule_eq_span (d e : ↥(D.block f.infinity)) (hde : d ≠ e)
    (p : Ω) (hdp : (d : Ω) ∈ D.block p) (hep : (e : Ω) ∈ D.block p)
    (hop : f.origin ∈ D.block p) :
    C.planeSubmodule t ht0 ht1 p hop =
      Submodule.span K {C.directionVector hl hq d,C.directionVector hl hq e} := by
  apply le_antisymm
  · intro v hv
    let x := C.coords.symm v
    have hxp : (x : Ω) ∈ D.block p := hv
    have hex : (e : Ω) ≠ x := fun he => x.property (he ▸ e.property)
    have hdo : (d : Ω) ≠ f.origin := fun he => f.origin_not_mem (he ▸ d.property)
    obtain ⟨y,hyex,hydo⟩ := D.coplanar_lines_meet hl hex hdo hep hxp hdp hop
    have hy : y ∉ D.block f.infinity := by
      intro hy
      have hye := (D.infinity_on_line e.property x.property hyex).mp hy
      have hyd := (D.infinity_on_line d.property f.origin_not_mem hydo).mp hy
      exact hde (Subtype.ext (hyd.symm.trans hye))
    let y' : f.Affine := ⟨y,hy⟩
    obtain ⟨r,hr⟩ := (C.axis_line hl hq d y').mp hydo
    have hey : (e : Ω) ≠ y := fun he => hy (he ▸ e.property)
    have hL : D.line e y = D.line e x := D.line_eq_of_mem hex hyex hey
    obtain ⟨s,hs⟩ := (C.parallel_line hl hq t ht0 ht1 e y' x).mp
      (hL.symm ▸ D.right_mem_line _ _)
    apply Submodule.mem_span_pair.mpr
    refine ⟨r,s,?_⟩
    rw [← hr,← hs]
    exact C.coords.apply_symm_apply v
  · apply Submodule.span_le.mpr
    intro v hv
    rcases hv with rfl | rfl
    · exact (C.directionVector_mem_planeSubmodule hl hq t ht0 ht1 p hop d).mpr hdp
    · exact (C.directionVector_mem_planeSubmodule hl hq t ht0 ht1 p hop e).mpr hep

/-- All lines in the infinity plane have their homogeneous vector equations. -/
theorem infinity_line (d e x : ↥(D.block f.infinity)) :
    C.directionVector hl hq x ∈ Submodule.span K
      {C.directionVector hl hq d,C.directionVector hl hq e} ↔ (x : Ω) ∈ D.line d e := by
  by_cases hde : d = e
  · subst e
    rw [show ({C.directionVector hl hq d,C.directionVector hl hq d} : Set V) =
      {C.directionVector hl hq d} by ext; simp,
      Submodule.mem_span_singleton,D.line_eq_singleton hq,Set.mem_singleton_iff]
    constructor
    · rintro ⟨r,hr⟩
      exact congrArg Subtype.val (C.direction_eq_of_smul hl hq d x r hr.symm)
    · intro he
      have hh : x = d := Subtype.ext he
      subst x
      exact ⟨1,one_smul _ _⟩
  · obtain ⟨p,hdp,hep,hop⟩ := D.exists_block_of_three hl (by omega) d e f.origin
    have hp : p ≠ f.infinity := fun he => f.origin_not_mem (he ▸ hop)
    have hde' : (d : Ω) ≠ e := fun he => hde (Subtype.ext he)
    have hi := D.intersection_eq_line hl hp ⟨hdp,d.property⟩ ⟨hep,e.property⟩ hde'
    rw [← C.planeSubmodule_eq_span hl hq t ht0 ht1 d e hde p hdp hep hop,
      C.directionVector_mem_planeSubmodule,← hi]
    exact ⟨fun hh => ⟨hh,x.property⟩,fun hh => hh.1⟩

local instance : DecidablePred (· ∈ D.block f.infinity) := Classical.decPred _

omit t ht0 ht1 in
/-- Homogenization uses the actual infinite directions of the source geometry. -/
@[expose] def homogeneousVector (x : Ω) : K × V :=
  if hx : x ∈ D.block f.infinity then (0,C.directionVector hl hq ⟨x,hx⟩)
  else (1,C.coords ⟨x,hx⟩)

omit t ht0 ht1 in
theorem homogeneousVector_affine (a : f.Affine) :
    C.homogeneousVector hl hq a = (1,C.coords a) := by
  simp only [homogeneousVector,dif_neg a.property]

omit t ht0 ht1 in
theorem homogeneousVector_direction (d : ↥(D.block f.infinity)) :
    C.homogeneousVector hl hq d = (0,C.directionVector hl hq d) := by
  simp only [homogeneousVector,dif_pos d.property]

omit t ht0 ht1 in
theorem homogeneousVector_ne_zero (x : Ω) : C.homogeneousVector hl hq x ≠ 0 := by
  by_cases hx : x ∈ D.block f.infinity
  · rw [show C.homogeneousVector hl hq x = (0,C.directionVector hl hq ⟨x,hx⟩) from
      C.homogeneousVector_direction hl hq ⟨x,hx⟩]
    exact fun he => C.directionVector_ne_zero hl hq ⟨x,hx⟩ (congrArg Prod.snd he)
  · rw [show C.homogeneousVector hl hq x = (1,C.coords ⟨x,hx⟩) from
      C.homogeneousVector_affine hl hq ⟨x,hx⟩]
    exact fun he => one_ne_zero (congrArg Prod.fst he)

omit t ht0 ht1 in
@[expose] def projectivePoint (x : Ω) : Projectivization K (K × V) :=
  Projectivization.mk K (C.homogeneousVector hl hq x) (C.homogeneousVector_ne_zero hl hq x)

omit t ht0 ht1 in
theorem projectivePoint_eq_iff (x y : Ω) :
    C.projectivePoint hl hq x = C.projectivePoint hl hq y ↔
      ∃ r : K, r • C.homogeneousVector hl hq y = C.homogeneousVector hl hq x :=
  mk_eq_mk_iff' _ _ _ _ _

omit t ht0 ht1 in
theorem projectivePoint_injective : Function.Injective (C.projectivePoint hl hq) := by
  intro x y he
  obtain ⟨r,hr⟩ := (C.projectivePoint_eq_iff hl hq x y).mp he
  by_cases hx : x ∈ D.block f.infinity
  · have hd : C.homogeneousVector hl hq x = (0,C.directionVector hl hq ⟨x,hx⟩) :=
      C.homogeneousVector_direction hl hq ⟨x,hx⟩
    by_cases hy : y ∈ D.block f.infinity
    · rw [hd,show C.homogeneousVector hl hq y = (0,C.directionVector hl hq ⟨y,hy⟩) from
        C.homogeneousVector_direction hl hq ⟨y,hy⟩] at hr
      exact congrArg Subtype.val (C.direction_eq_of_smul hl hq ⟨y,hy⟩ ⟨x,hx⟩ r
        (congrArg Prod.snd hr).symm)
    · rw [hd,show C.homogeneousVector hl hq y = (1,C.coords ⟨y,hy⟩) from
        C.homogeneousVector_affine hl hq ⟨y,hy⟩] at hr
      have hr0 : r = 0 := by
        have hh := congrArg Prod.fst hr
        change r*1 = 0 at hh
        simpa only [mul_one] using hh
      have hh := congrArg Prod.snd hr
      change r • C.coords ⟨y,hy⟩ = C.directionVector hl hq ⟨x,hx⟩ at hh
      rw [hr0,zero_smul] at hh
      exact (C.directionVector_ne_zero hl hq ⟨x,hx⟩ hh.symm).elim
  · have ha : C.homogeneousVector hl hq x = (1,C.coords ⟨x,hx⟩) :=
      C.homogeneousVector_affine hl hq ⟨x,hx⟩
    by_cases hy : y ∈ D.block f.infinity
    · rw [ha,show C.homogeneousVector hl hq y = (0,C.directionVector hl hq ⟨y,hy⟩) from
        C.homogeneousVector_direction hl hq ⟨y,hy⟩] at hr
      have hh := congrArg Prod.fst hr
      change r*0 = 1 at hh
      exact (zero_ne_one (by simpa only [mul_zero] using hh)).elim
    · rw [ha,show C.homogeneousVector hl hq y = (1,C.coords ⟨y,hy⟩) from
        C.homogeneousVector_affine hl hq ⟨y,hy⟩] at hr
      have hr1 : r = 1 := by
        have hh := congrArg Prod.fst hr
        change r*1 = 1 at hh
        simpa only [mul_one] using hh
      have hh := congrArg Prod.snd hr
      change r • C.coords ⟨y,hy⟩ = C.coords ⟨x,hx⟩ at hh
      rw [hr1,one_smul] at hh
      exact congrArg Subtype.val (C.coords.injective hh).symm

omit t ht0 ht1 in
theorem projectivePoint_surjective : Function.Surjective (C.projectivePoint hl hq) := by
  intro p
  induction p using Projectivization.ind with | h v hv =>
  by_cases hc : v.1 = 0
  · have hv2 : v.2 ≠ 0 := fun hh => hv (Prod.ext hc hh)
    let a := C.coords.symm v.2
    have hoa : f.origin ≠ (a : Ω) := by
      intro he
      have hh : a = f.originPoint := Subtype.ext he.symm
      exact hv2 ((C.coords.apply_symm_apply v.2).symm.trans (by change C.coords a = 0; rw [hh,C.origin_zero]))
    obtain ⟨d,hdl,hdI⟩ := D.line_meets_block hl (by omega) hoa f.infinity
    have hdo : d ≠ f.origin := fun he => f.origin_not_mem (he ▸ hdI)
    have hL : D.line d f.origin = D.line f.origin a :=
      D.line_eq_of_mem_of_mem hoa hdl (D.left_mem_line _ _) hdo
    obtain ⟨r,hr⟩ := (C.axis_line hl hq ⟨d,hdI⟩ a).mp (hL.symm ▸ D.right_mem_line _ _)
    refine ⟨d,?_⟩
    symm
    apply (mk_eq_mk_iff' _ _ _ _ _).mpr
    refine ⟨r,?_⟩
    rw [show C.homogeneousVector hl hq d = (0,C.directionVector hl hq ⟨d,hdI⟩) from
      C.homogeneousVector_direction hl hq ⟨d,hdI⟩]
    exact Prod.ext (by change r*0 = v.1; rw [mul_zero,hc])
      (hr.symm.trans (C.coords.apply_symm_apply v.2))
  · let a := C.coords.symm (v.1⁻¹ • v.2)
    refine ⟨a,?_⟩
    symm
    apply (mk_eq_mk_iff' _ _ _ _ _).mpr
    refine ⟨v.1,?_⟩
    rw [show C.homogeneousVector hl hq a = (1,C.coords a) from C.homogeneousVector_affine hl hq a]
    refine Prod.ext (mul_one _) ?_
    change v.1 • C.coords (C.coords.symm (v.1⁻¹ • v.2)) = v.2
    rw [Equiv.apply_symm_apply,smul_smul,mul_inv_cancel₀ hc,one_smul]

omit t ht0 ht1 in
@[expose] def projectiveEquiv : Ω ≃ Projectivization K (K × V) :=
  Equiv.ofBijective (C.projectivePoint hl hq)
    ⟨C.projectivePoint_injective hl hq,C.projectivePoint_surjective hl hq⟩

omit t ht0 ht1 in
theorem homogeneous_span_finrank (a b : Ω) (hab : a ≠ b) :
    Module.finrank K (Submodule.span K {C.homogeneousVector hl hq a,C.homogeneousVector hl hq b}) = 2 := by
  have hh := (C.projectivePoint_injective hl hq).ne hab
  change Projectivization.mk _ _ _ ≠ Projectivization.mk _ _ _ at hh
  rw [← independent_pair_iff_ne,independent_mk_iff_LinearIndependent] at hh
  rw [← Matrix.range_cons_cons_empty _ _ ![]]
  simpa only [Fintype.card_fin] using finrank_span_eq_card hh

theorem homogeneous_direction_line (d : ↥(D.block f.infinity)) (a : f.Affine) (x : Ω) :
    C.homogeneousVector hl hq x ∈ Submodule.span K
      {C.homogeneousVector hl hq d,C.homogeneousVector hl hq a} ↔ x ∈ D.line d a := by
  rw [C.homogeneousVector_direction,C.homogeneousVector_affine,Submodule.mem_span_pair]
  by_cases hx : x ∈ D.block f.infinity
  · let e : ↥(D.block f.infinity) := ⟨x,hx⟩
    rw [show C.homogeneousVector hl hq x = (0,C.directionVector hl hq e) from
      C.homogeneousVector_direction hl hq e]
    have hxl : x ∈ D.line d a ↔ e = d := by
      constructor
      · intro hh
        exact Subtype.ext ((D.infinity_on_line d.property a.property hh).mp hx)
      · intro hh
        rw [show x = (d : Ω) from congrArg Subtype.val hh]
        exact D.left_mem_line _ _
    rw [hxl]
    constructor
    · rintro ⟨r,s,hrs⟩
      have hs : s = 0 := by
        have hh := congrArg Prod.fst hrs
        change r*0+s*1 = 0 at hh
        simpa only [mul_zero,mul_one,zero_add] using hh
      have hh := congrArg Prod.snd hrs
      change r • C.directionVector hl hq d + s • C.coords a = C.directionVector hl hq e at hh
      rw [hs,zero_smul,add_zero] at hh
      exact C.direction_eq_of_smul hl hq d e r hh.symm
    · intro he
      rw [he]
      exact ⟨1,0,by simp⟩
  · let b : f.Affine := ⟨x,hx⟩
    rw [show C.homogeneousVector hl hq x = (1,C.coords b) from C.homogeneousVector_affine hl hq b]
    rw [C.parallel_line hl hq t ht0 ht1 d a b]
    constructor
    · rintro ⟨r,s,hrs⟩
      have hs : s = 1 := by
        have hh := congrArg Prod.fst hrs
        change r*0+s*1 = 1 at hh
        simpa only [mul_zero,mul_one,zero_add] using hh
      have hh := congrArg Prod.snd hrs
      change r • C.directionVector hl hq d + s • C.coords a = C.coords b at hh
      rw [hs,one_smul,add_comm] at hh
      exact ⟨r,hh.symm⟩
    · rintro ⟨r,hr⟩
      refine ⟨r,1,Prod.ext (by simp) ?_⟩
      change r • C.directionVector hl hq d + 1 • C.coords a = C.coords b
      rw [one_smul,add_comm,hr]

theorem homogeneous_infinity_line (d e : ↥(D.block f.infinity)) (x : Ω) :
    C.homogeneousVector hl hq x ∈ Submodule.span K
      {C.homogeneousVector hl hq d,C.homogeneousVector hl hq e} ↔ x ∈ D.line d e := by
  rw [C.homogeneousVector_direction,C.homogeneousVector_direction,Submodule.mem_span_pair]
  by_cases hx : x ∈ D.block f.infinity
  · let z : ↥(D.block f.infinity) := ⟨x,hx⟩
    rw [show C.homogeneousVector hl hq x = (0,C.directionVector hl hq z) from
      C.homogeneousVector_direction hl hq z]
    rw [← C.infinity_line hl hq t ht0 ht1 d e z,Submodule.mem_span_pair]
    exact ⟨fun ⟨r,s,hrs⟩ => ⟨r,s,congrArg Prod.snd hrs⟩,
      fun ⟨r,s,hrs⟩ => ⟨r,s,Prod.ext (by simp) hrs⟩⟩
  · rw [show C.homogeneousVector hl hq x = (1,C.coords ⟨x,hx⟩) from
      C.homogeneousVector_affine hl hq ⟨x,hx⟩]
    constructor
    · rintro ⟨r,s,hrs⟩
      have hh := congrArg Prod.fst hrs
      change r*0+s*0 = 1 at hh
      exact (zero_ne_one (by simpa only [mul_zero,add_zero] using hh)).elim
    · intro hh
      exact (hx (D.line_subset_block d.property e.property hh)).elim

/-- The affine chart extends to a single projective chart preserving all
source lines, including those entirely at infinity. -/
theorem projectiveEquiv_line (a b x : Ω) :
    (C.projectiveEquiv hl hq x).submodule ≤
      (C.projectiveEquiv hl hq a).submodule ⊔ (C.projectiveEquiv hl hq b).submodule ↔
        x ∈ D.line a b := by
  change (C.projectivePoint hl hq x).submodule ≤
    (C.projectivePoint hl hq a).submodule ⊔ (C.projectivePoint hl hq b).submodule ↔ _
  simp only [projectivePoint,submodule_mk,← Submodule.span_insert,Submodule.span_singleton_le_iff_mem]
  by_cases hab : a = b
  · subst b
    rw [show ({C.homogeneousVector hl hq a,C.homogeneousVector hl hq a} : Set _) =
      {C.homogeneousVector hl hq a} by ext; simp,
      Submodule.mem_span_singleton,← C.projectivePoint_eq_iff]
    rw [(C.projectivePoint_injective hl hq).eq_iff,D.line_eq_singleton hq,Set.mem_singleton_iff]
  have hfinite (a b : Ω) (hab : a ≠ b) (ha : a ∉ D.block f.infinity) :
      ∃ W : Submodule K (K × V), Module.finrank K W = 2 ∧
        ∀ x, C.homogeneousVector hl hq x ∈ W ↔ x ∈ D.line a b := by
    obtain ⟨d,hdL,hdI⟩ := D.line_meets_block hl (by omega) hab f.infinity
    have hda : d ≠ a := fun he => ha (he ▸ hdI)
    have hL : D.line d a = D.line a b :=
      D.line_eq_of_mem_of_mem hab hdL (D.left_mem_line _ _) hda
    refine ⟨Submodule.span K {C.homogeneousVector hl hq d,C.homogeneousVector hl hq a},
      C.homogeneous_span_finrank hl hq d a hda,?_⟩
    intro x
    exact (C.homogeneous_direction_line hl hq t ht0 ht1 ⟨d,hdI⟩ ⟨a,ha⟩ x).trans (by rw [hL])
  have hW : ∃ W : Submodule K (K × V), Module.finrank K W = 2 ∧
      ∀ x, C.homogeneousVector hl hq x ∈ W ↔ x ∈ D.line a b := by
    by_cases ha : a ∈ D.block f.infinity
    · by_cases hb : b ∈ D.block f.infinity
      · exact ⟨_,C.homogeneous_span_finrank hl hq a b hab,
          C.homogeneous_infinity_line hl hq t ht0 ht1 ⟨a,ha⟩ ⟨b,hb⟩⟩
      · obtain ⟨W,hW,hWx⟩ := hfinite b a (Ne.symm hab) hb
        exact ⟨W,hW,fun x => (hWx x).trans (by rw [D.line_comm])⟩
    · exact hfinite a b hab ha
  obtain ⟨W,hW,hWx⟩ := hW
  have hle : Submodule.span K {C.homogeneousVector hl hq a,C.homogeneousVector hl hq b} ≤ W := by
    apply Submodule.span_le.mpr
    intro v hv
    rcases hv with rfl | rfl
    · exact (hWx a).mpr (D.left_mem_line _ _)
    · exact (hWx b).mpr (D.right_mem_line _ _)
  have : Module.Finite K W := Module.finite_of_finrank_eq_succ hW
  rw [Submodule.eq_of_le_of_finrank_eq hle ((C.homogeneous_span_finrank hl hq a b hab).trans hW.symm)]
  exact hWx x

omit hl hq t ht0 ht1 in
/-- Normalize a constructed affine line chart by translating its origin to zero. -/
@[expose] def ofLineEquiv (E : f.Affine ≃ V)
    (hE : ∀ a b x : f.Affine, (x : Ω) ∈ D.line a b ↔
      ∃ r : K, E x = E a+r•(E b-E a)) : FieldChart f K V where
  coords :=
    { toFun := fun x => E x-E f.originPoint
      invFun := fun v => E.symm (v+E f.originPoint)
      left_inv := fun x => by
        change E.symm (E x-E f.originPoint+E f.originPoint) = x
        rw [sub_add_cancel,Equiv.symm_apply_apply]
      right_inv := fun v => by
        change E (E.symm (v+E f.originPoint))-E f.originPoint = v
        rw [Equiv.apply_symm_apply,add_sub_cancel_right] }
  origin_zero := sub_self _
  line_iff a b x := by
    change (x : Ω) ∈ D.line a b ↔ ∃ r : K,
      E x-E f.originPoint = E a-E f.originPoint +
        r • ((E b-E f.originPoint)-(E a-E f.originPoint))
    rw [hE]
    apply exists_congr
    intro r
    rw [show (E b-E f.originPoint)-(E a-E f.originPoint) = E b-E a by abel]
    rw [show E a-E f.originPoint+r•(E b-E a) =
      (E a+r•(E b-E a))-E f.originPoint by abel]
    exact sub_left_inj.symm

end FieldChart
end Theory.GroupAction.SymplecticRankThree.AffineFrame
