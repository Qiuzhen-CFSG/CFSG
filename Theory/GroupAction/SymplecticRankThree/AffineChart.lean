module
public import Theory.GroupAction.SymplecticRankThree.ProjectiveIncidence

/-!
# Affine Cartesian charts from Higman's incidence geometry

Delete one polar block as the plane at infinity. Choose three noncollinear
points in that plane and an affine origin. A line with center outside a
plane has a unique intersection with it. Parallel projection therefore
splits the affine three-space into an affine plane and a transverse axis;
two parallel pencils split the plane into its two axes. The resulting
bijection uses actual source points on the three axes. Each axis has q
points, and the coordinate fibers have their literal line/plane incidence
formulas. The construction and all counts include q=2.

This constructs Cartesian coordinates from incidence, not field arithmetic.
Proving field-linear equations for general lines is still necessary for
projective coordinatization and the nonbinary recognition theorem.

Source: Higman, *Finite permutation groups of rank 3* (1964), Lemma 10,
pp.153–154, the coordinatization step after projective incidence. The
construction below expands that step by elementary parallel projection.
-/

public noncomputable section
namespace Theory.GroupAction.SymplecticRankThree.PolarityDesign
variable {Ω : Type*} [Finite Ω] {q : ℕ} (D : PolarityDesign Ω q)
variable (hline : ∀ a b, a ≠ b → (D.line a b).ncard = q+1) (hq : 2 ≤ q)

include hq in
theorem line_eq_singleton (a : Ω) : D.line a a = {a} := by
  ext x
  constructor
  · intro hx
    by_contra hxa
    have hsub : D.block a ⊆ D.block x := fun z hz => D.symm (hx z (D.symm hz) (D.symm hz))
    have he : D.block a ∩ D.block x = D.block a := Set.inter_eq_left.mpr hsub
    have hc := D.intersection_card (Ne.symm hxa)
    change (D.block a ∩ D.block x).ncard = q+1 at hc
    rw [he,show (D.block a).ncard = q^2+q+1 from D.block_card a] at hc
    nlinarith
  · rintro rfl
    exact D.left_mem_line x x

include hline hq in
theorem existsUnique_line_block {a x p : Ω} (ha : a ∉ D.block p) (hax : a ≠ x) :
    ∃! y, y ∈ D.line a x ∧ y ∈ D.block p := by
  obtain ⟨y,hy,hyp⟩ := D.line_meets_block hline (by omega) hax p
  refine ⟨y,⟨hy,hyp⟩,?_⟩
  intro z hz
  exact D.line_block_unique hax ha hz.1 hy hz.2 hyp

@[expose] def project (p a : Ω) (ha : a ∉ D.block p) (x : Ω) (hax : a ≠ x) : Ω :=
  (D.existsUnique_line_block hline hq ha hax).choose

theorem project_mem_line (p a : Ω) (ha : a ∉ D.block p) (x : Ω) (hax : a ≠ x) :
    D.project hline hq p a ha x hax ∈ D.line a x :=
  (D.existsUnique_line_block hline hq ha hax).choose_spec.1.1

theorem project_mem_block (p a : Ω) (ha : a ∉ D.block p) (x : Ω) (hax : a ≠ x) :
    D.project hline hq p a ha x hax ∈ D.block p :=
  (D.existsUnique_line_block hline hq ha hax).choose_spec.1.2

theorem project_eq (p a : Ω) (ha : a ∉ D.block p) (x : Ω) (hax : a ≠ x)
    {y : Ω} (hyl : y ∈ D.line a x) (hyp : y ∈ D.block p) :
    D.project hline hq p a ha x hax = y :=
  ((D.existsUnique_line_block hline hq ha hax).choose_spec.2 y ⟨hyl,hyp⟩).symm

theorem project_fixed (p a : Ω) (ha : a ∉ D.block p) (x : Ω) (hx : x ∈ D.block p) :
    D.project hline hq p a ha x (fun he => ha (he.symm ▸ hx)) = x :=
  D.project_eq hline hq p a ha x _ (D.right_mem_line a x) hx

theorem project_ne_center (p a : Ω) (ha : a ∉ D.block p) (x : Ω) (hax : a ≠ x) :
    a ≠ D.project hline hq p a ha x hax := by
  intro he
  exact ha (he.symm ▸ D.project_mem_block hline hq p a ha x hax)

theorem project_line_eq (p a : Ω) (ha : a ∉ D.block p) (x : Ω) (hax : a ≠ x) :
    D.line a (D.project hline hq p a ha x hax) = D.line a x :=
  D.line_eq_of_mem hax (D.project_mem_line hline hq p a ha x hax)
    (D.project_ne_center hline hq p a ha x hax)

include hline hq in
theorem existsUnique_block_through_line {i j x : Ω} (hij : i ≠ j)
    (hx : x ∉ D.line i j) :
    ∃! p, i ∈ D.block p ∧ j ∈ D.block p ∧ x ∈ D.block p :=
  D.existsUnique_block_of_noncollinear hline (by omega) hij hx

@[expose] def plane (i j x : Ω) (hij : i ≠ j) (hx : x ∉ D.line i j) : Ω :=
  (D.existsUnique_block_through_line hline hq hij hx).choose

theorem plane_spec (i j x : Ω) (hij : i ≠ j) (hx : x ∉ D.line i j) :
    i ∈ D.block (D.plane hline hq i j x hij hx) ∧
    j ∈ D.block (D.plane hline hq i j x hij hx) ∧
    x ∈ D.block (D.plane hline hq i j x hij hx) :=
  (D.existsUnique_block_through_line hline hq hij hx).choose_spec.1

theorem plane_eq (i j x : Ω) (hij : i ≠ j) (hx : x ∉ D.line i j)
    {p : Ω} (hi : i ∈ D.block p) (hj : j ∈ D.block p) (hxp : x ∈ D.block p) :
    D.plane hline hq i j x hij hx = p :=
  ((D.existsUnique_block_through_line hline hq hij hx).choose_spec.2 p ⟨hi,hj,hxp⟩).symm

theorem infinity_on_line {a x z p : Ω} (ha : a ∈ D.block p) (hx : x ∉ D.block p)
    (hz : z ∈ D.line a x) : z ∈ D.block p ↔ z = a := by
  constructor
  · intro hzp
    exact D.line_block_unique (a := x) (b := a) (fun he => hx (he.symm ▸ ha)) hx
      (D.line_comm a x ▸ hz) (D.right_mem_line x a) hzp ha
  · rintro rfl
    exact ha

theorem project_not_mem_infinity {p a s x : Ω} (ha : a ∉ D.block p)
    (has : a ∈ D.block s) (hxs : x ∉ D.block s) :
    D.project hline hq p a ha x (fun he => hxs (he ▸ has)) ∉ D.block s := by
  intro hh
  have he := (D.infinity_on_line has hxs (D.project_mem_line hline hq p a ha x _)).mp hh
  exact D.project_ne_center hline hq p a ha x _ he.symm

end Theory.GroupAction.SymplecticRankThree.PolarityDesign

namespace Theory.GroupAction.SymplecticRankThree
variable {Ω : Type*} [Finite Ω] {q : ℕ}

/-- Three independent directions in the infinity plane and an affine origin. -/
structure AffineFrame (D : PolarityDesign Ω q) where
  infinity : Ω
  i : Ω
  j : Ω
  k : Ω
  origin : Ω
  i_mem : i ∈ D.block infinity
  j_mem : j ∈ D.block infinity
  k_mem : k ∈ D.block infinity
  ij_ne : i ≠ j
  k_not_line : k ∉ D.line i j
  origin_not_mem : origin ∉ D.block infinity

namespace PolarityDesign
variable (D : PolarityDesign Ω q)
variable (hline : ∀ a b, a ≠ b → (D.line a b).ncard = q+1) (hq : 2 ≤ q)

include hline hq in
theorem exists_affineFrame (hdegree : Nat.card Ω = q^3+q^2+q+1) (p : Ω) :
    ∃ f : AffineFrame D, f.infinity = p := by
  obtain ⟨i,hi,j,hj,hij⟩ := (Set.one_lt_ncard).mp
    (show 1 < (D.block p).ncard by
      rw [show (D.block p).ncard = q^2+q+1 from D.block_card p]
      nlinarith)
  have hnot : ¬ D.block p ⊆ D.line i j := by
    intro hh
    have hn := Set.ncard_le_ncard hh
    rw [hline i j hij,show (D.block p).ncard = q^2+q+1 from D.block_card p] at hn
    nlinarith
  obtain ⟨k,hk,hkL⟩ := Set.not_subset.mp hnot
  have hout : ¬ (Set.univ : Set Ω) ⊆ D.block p := by
    intro hh
    have hn := Set.ncard_le_ncard hh
    rw [Set.ncard_univ,hdegree,show (D.block p).ncard = q^2+q+1 from D.block_card p] at hn
    have : 0 < q^3 := pow_pos (by omega) _
    omega
  obtain ⟨o,_,ho⟩ := Set.not_subset.mp hout
  exact ⟨⟨p,i,j,k,o,hi,hj,hk,hij,hkL,ho⟩,rfl⟩

end PolarityDesign

namespace AffineFrame
variable {D : PolarityDesign Ω q} (f : AffineFrame D)
variable (hline : ∀ a b, a ≠ b → (D.line a b).ncard = q+1) (hq : 2 ≤ q)

abbrev Affine := {x : Ω // x ∉ D.block f.infinity}

@[expose] def originPoint : f.Affine := ⟨f.origin,f.origin_not_mem⟩

theorem affine_not_line (x : f.Affine) : (x : Ω) ∉ D.line f.i f.j :=
  fun hx => x.property (D.line_subset_block f.i_mem f.j_mem hx)

@[expose] def level (x : f.Affine) : Ω :=
  D.plane hline hq f.i f.j x f.ij_ne (f.affine_not_line x)

theorem level_spec (x : f.Affine) :
    f.i ∈ D.block (f.level hline hq x) ∧ f.j ∈ D.block (f.level hline hq x) ∧
      (x : Ω) ∈ D.block (f.level hline hq x) :=
  D.plane_spec hline hq f.i f.j x f.ij_ne (f.affine_not_line x)

theorem k_not_level (x : f.Affine) : f.k ∉ D.block (f.level hline hq x) := by
  intro hk
  have hi := (f.level_spec hline hq x).1
  have hj := (f.level_spec hline hq x).2.1
  have he : f.level hline hq x = f.infinity :=
    (D.plane_eq hline hq f.i f.j f.k f.ij_ne f.k_not_line hi hj hk).symm.trans
      (D.plane_eq hline hq f.i f.j f.k f.ij_ne f.k_not_line f.i_mem f.j_mem f.k_mem)
  have hx := (f.level_spec hline hq x).2.2
  rw [he] at hx
  exact x.property hx

theorem level_eq_of_mem (x y : f.Affine) (hy : (y : Ω) ∈ D.block (f.level hline hq x)) :
    f.level hline hq y = f.level hline hq x :=
  D.plane_eq hline hq f.i f.j y f.ij_ne (f.affine_not_line y)
    (f.level_spec hline hq x).1 (f.level_spec hline hq x).2.1 hy

abbrev Base := {x : f.Affine // (x : Ω) ∈ D.block (f.level hline hq f.originPoint)}
abbrev AxisAt (d : Ω) := {x : f.Affine // (x : Ω) ∈ D.line d f.origin}
abbrev Axis := f.AxisAt f.k

theorem k_ne_affine (x : f.Affine) : f.k ≠ (x : Ω) :=
  fun he => x.property (he ▸ f.k_mem)

@[expose] def foot (x : f.Affine) : f.Base hline hq :=
  ⟨⟨D.project hline hq (f.level hline hq f.originPoint) f.k
    (f.k_not_level hline hq f.originPoint) x (f.k_ne_affine x),
    D.project_not_mem_infinity hline hq _ f.k_mem x.property⟩,
    D.project_mem_block hline hq _ _ (f.k_not_level hline hq f.originPoint) _ (f.k_ne_affine x)⟩

theorem foot_line (x : f.Affine) :
    D.line f.k (f.foot hline hq x : Ω) = D.line f.k x :=
  D.project_line_eq hline hq _ _ (f.k_not_level hline hq f.originPoint) _ (f.k_ne_affine x)

@[expose] def height (x : f.Affine) : f.Axis :=
  ⟨⟨D.project hline hq (f.level hline hq x) f.k (f.k_not_level hline hq x)
    f.origin (f.k_ne_affine f.originPoint),
    D.project_not_mem_infinity hline hq _ f.k_mem f.origin_not_mem⟩,
    D.project_mem_line hline hq _ _ (f.k_not_level hline hq x) _ (f.k_ne_affine f.originPoint)⟩

theorem height_mem_level (x : f.Affine) :
    (f.height hline hq x : Ω) ∈ D.block (f.level hline hq x) :=
  D.project_mem_block hline hq _ _ (f.k_not_level hline hq x) _ (f.k_ne_affine f.originPoint)

theorem height_level (x : f.Affine) :
    f.level hline hq (f.height hline hq x).val = f.level hline hq x :=
  f.level_eq_of_mem hline hq x _ (f.height_mem_level hline hq x)

@[expose] def assemble (y : f.Base hline hq) (z : f.Axis) : f.Affine :=
  ⟨D.project hline hq (f.level hline hq z.val) f.k (f.k_not_level hline hq z.val)
    y.val (f.k_ne_affine y.val),
    D.project_not_mem_infinity hline hq _ f.k_mem y.val.property⟩

theorem assemble_line (y : f.Base hline hq) (z : f.Axis) :
    D.line f.k (f.assemble hline hq y z) = D.line f.k (y : Ω) :=
  D.project_line_eq hline hq _ _ (f.k_not_level hline hq z.val) _ (f.k_ne_affine y.val)

theorem assemble_level (y : f.Base hline hq) (z : f.Axis) :
    f.level hline hq (f.assemble hline hq y z) = f.level hline hq z.val :=
  f.level_eq_of_mem hline hq z.val _ (D.project_mem_block hline hq _ _
    (f.k_not_level hline hq z.val) _ (f.k_ne_affine y.val))

@[simp] theorem foot_assemble (y : f.Base hline hq) (z : f.Axis) :
    f.foot hline hq (f.assemble hline hq y z) = y := by
  apply Subtype.ext
  apply Subtype.ext
  refine D.project_eq hline hq _ _ (f.k_not_level hline hq f.originPoint) _
    (f.k_ne_affine (f.assemble hline hq y z)) ?_ ?_
  · rw [f.assemble_line]
    exact D.right_mem_line _ _
  · exact y.property

@[simp] theorem height_assemble (y : f.Base hline hq) (z : f.Axis) :
    f.height hline hq (f.assemble hline hq y z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  refine D.project_eq hline hq _ _ (f.k_not_level hline hq (f.assemble hline hq y z)) _
    (f.k_ne_affine f.originPoint) ?_ ?_
  · exact z.property
  · rw [f.assemble_level]
    exact (f.level_spec hline hq z.val).2.2

@[simp] theorem assemble_foot_height (x : f.Affine) :
    f.assemble hline hq (f.foot hline hq x) (f.height hline hq x) = x := by
  apply Subtype.ext
  refine D.project_eq hline hq _ _ (f.k_not_level hline hq (f.height hline hq x).val) _
    (f.k_ne_affine (f.foot hline hq x).val) ?_ ?_
  · rw [f.foot_line]
    exact D.right_mem_line _ _
  · rw [f.height_level]
    exact (f.level_spec hline hq x).2.2

/-- Parallel projection constructs a Cartesian product of an affine plane
and a transverse affine line. Both components are original point fibers. -/
@[expose] def planeAxisEquiv : f.Affine ≃ f.Base hline hq × f.Axis where
  toFun x := (f.foot hline hq x, f.height hline hq x)
  invFun yz := f.assemble hline hq yz.1 yz.2
  left_inv := f.assemble_foot_height hline hq
  right_inv yz := Prod.ext (f.foot_assemble hline hq yz.1 yz.2)
    (f.height_assemble hline hq yz.1 yz.2)

theorem i_ne_affine (x : f.Affine) : f.i ≠ (x : Ω) :=
  fun he => x.property (he ▸ f.i_mem)

theorem j_ne_affine (x : f.Affine) : f.j ≠ (x : Ω) :=
  fun he => x.property (he ▸ f.j_mem)

theorem cross_existsUnique (a b : f.Base hline hq) :
    ∃! x : Ω, x ∈ D.line f.j (a : Ω) ∧ x ∈ D.line f.i (b : Ω) := by
  have hj := (f.level_spec hline hq f.originPoint).2.1
  have hi := (f.level_spec hline hq f.originPoint).1
  obtain ⟨x,hxa,hxb⟩ := D.coplanar_lines_meet hline (f.j_ne_affine a.val)
    (f.i_ne_affine b.val) hj a.property hi b.property
  refine ⟨x,⟨hxa,hxb⟩,?_⟩
  intro y hy
  by_contra hne
  have he : D.line f.j (a : Ω) = D.line f.i (b : Ω) :=
    (D.line_eq_of_mem_of_mem (f.j_ne_affine a.val) hy.1 hxa hne).symm.trans
      (D.line_eq_of_mem_of_mem (f.i_ne_affine b.val) hy.2 hxb hne)
  have hji : f.j ∈ D.line f.i (b : Ω) := he ▸ D.left_mem_line f.j (a : Ω)
  exact f.ij_ne ((D.infinity_on_line f.i_mem b.val.property hji).mp f.j_mem).symm

@[expose] def cross (a b : f.Base hline hq) : f.Base hline hq := by
  let x := (f.cross_existsUnique hline hq a b).choose
  have hxl : x ∈ D.line f.j (a : Ω) := (f.cross_existsUnique hline hq a b).choose_spec.1.1
  have hxr : x ∈ D.line f.i (b : Ω) := (f.cross_existsUnique hline hq a b).choose_spec.1.2
  have hx : x ∉ D.block f.infinity := by
    intro hx
    have hxj := (D.infinity_on_line f.j_mem a.val.property hxl).mp hx
    have hxi := (D.infinity_on_line f.i_mem b.val.property hxr).mp hx
    exact f.ij_ne (hxi.symm.trans hxj)
  exact ⟨⟨x,hx⟩,D.line_subset_block (f.level_spec hline hq f.originPoint).2.1 a.property hxl⟩

theorem cross_mem_left (a b : f.Base hline hq) :
    (f.cross hline hq a b : Ω) ∈ D.line f.j (a : Ω) :=
  (f.cross_existsUnique hline hq a b).choose_spec.1.1

theorem cross_mem_right (a b : f.Base hline hq) :
    (f.cross hline hq a b : Ω) ∈ D.line f.i (b : Ω) :=
  (f.cross_existsUnique hline hq a b).choose_spec.1.2

theorem cross_eq (a b x : f.Base hline hq)
    (hl : (x : Ω) ∈ D.line f.j (a : Ω)) (hr : (x : Ω) ∈ D.line f.i (b : Ω)) :
    f.cross hline hq a b = x :=
  Subtype.ext (Subtype.ext ((f.cross_existsUnique hline hq a b).choose_spec.2 x ⟨hl,hr⟩).symm)

theorem cross_left_line (a b : f.Base hline hq) :
    D.line f.j (f.cross hline hq a b : Ω) = D.line f.j (a : Ω) :=
  D.line_eq_of_mem (f.j_ne_affine a.val) (f.cross_mem_left hline hq a b)
    (f.j_ne_affine (f.cross hline hq a b).val)

theorem cross_right_line (a b : f.Base hline hq) :
    D.line f.i (f.cross hline hq a b : Ω) = D.line f.i (b : Ω) :=
  D.line_eq_of_mem (f.i_ne_affine b.val) (f.cross_mem_right hline hq a b)
    (f.i_ne_affine (f.cross hline hq a b).val)

@[expose] def baseOrigin : f.Base hline hq :=
  ⟨f.originPoint,(f.level_spec hline hq f.originPoint).2.2⟩

abbrev AxisI := {x : f.Base hline hq // (x : Ω) ∈ D.line f.i f.origin}
abbrev AxisJ := {x : f.Base hline hq // (x : Ω) ∈ D.line f.j f.origin}

@[expose] def first (x : f.Base hline hq) : f.AxisI hline hq :=
  ⟨f.cross hline hq x (f.baseOrigin hline hq),f.cross_mem_right hline hq x (f.baseOrigin hline hq)⟩

@[expose] def second (x : f.Base hline hq) : f.AxisJ hline hq :=
  ⟨f.cross hline hq (f.baseOrigin hline hq) x,f.cross_mem_left hline hq (f.baseOrigin hline hq) x⟩

@[simp] theorem first_cross (a : f.AxisI hline hq) (b : f.AxisJ hline hq) :
    f.first hline hq (f.cross hline hq a.val b.val) = a := by
  apply Subtype.ext
  apply f.cross_eq hline hq
  · rw [f.cross_left_line]
    exact D.right_mem_line _ _
  · exact a.property

@[simp] theorem second_cross (a : f.AxisI hline hq) (b : f.AxisJ hline hq) :
    f.second hline hq (f.cross hline hq a.val b.val) = b := by
  apply Subtype.ext
  apply f.cross_eq hline hq
  · exact b.property
  · rw [f.cross_right_line]
    exact D.right_mem_line _ _

@[simp] theorem cross_first_second (x : f.Base hline hq) :
    f.cross hline hq (f.first hline hq x).val (f.second hline hq x).val = x := by
  apply f.cross_eq hline hq
  · change (x : Ω) ∈ D.line f.j (f.cross hline hq x (f.baseOrigin hline hq) : Ω)
    rw [f.cross_left_line]
    exact D.right_mem_line _ _
  · change (x : Ω) ∈ D.line f.i (f.cross hline hq (f.baseOrigin hline hq) x : Ω)
    rw [f.cross_right_line]
    exact D.right_mem_line _ _

/-- The two parallel pencils give coordinates on the base affine plane. -/
@[expose] def baseEquiv : f.Base hline hq ≃ f.AxisI hline hq × f.AxisJ hline hq where
  toFun x := (f.first hline hq x,f.second hline hq x)
  invFun ab := f.cross hline hq ab.1.val ab.2.val
  left_inv := f.cross_first_second hline hq
  right_inv ab := Prod.ext (f.first_cross hline hq ab.1 ab.2) (f.second_cross hline hq ab.1 ab.2)

/-- A Cartesian chart on the entire affine three-space, constructed from
incidence. No field operations or coordinate equivalence are inputs. -/
@[expose] def axisCoordinates :
    f.Affine ≃ (f.AxisI hline hq × f.AxisJ hline hq) × f.Axis :=
  (f.planeAxisEquiv hline hq).trans ((f.baseEquiv hline hq).prodCongr (Equiv.refl _))

@[simp] theorem axisCoordinates_apply (x : f.Affine) :
    f.axisCoordinates hline hq x =
      ((f.first hline hq (f.foot hline hq x),f.second hline hq (f.foot hline hq x)),
        f.height hline hq x) := rfl

theorem first_fiber (x : f.Base hline hq) (a : f.AxisI hline hq) :
    (x : Ω) ∈ D.line f.j (a : Ω) ↔ f.first hline hq x = a := by
  constructor
  · intro hx
    apply Subtype.ext
    apply f.cross_eq hline hq
    · have he := D.line_eq_of_mem (f.j_ne_affine a.val.val) hx (f.j_ne_affine x.val)
      exact he.symm ▸ D.right_mem_line f.j (a : Ω)
    · exact a.property
  · intro he
    have hx : (x : Ω) ∈ D.line f.j ((f.first hline hq x).val : Ω) := by
      change (x : Ω) ∈ D.line f.j (f.cross hline hq x (f.baseOrigin hline hq) : Ω)
      rw [f.cross_left_line]
      exact D.right_mem_line _ _
    simpa only [he] using hx

theorem second_fiber (x : f.Base hline hq) (b : f.AxisJ hline hq) :
    (x : Ω) ∈ D.line f.i (b : Ω) ↔ f.second hline hq x = b := by
  constructor
  · intro hx
    apply Subtype.ext
    apply f.cross_eq hline hq
    · exact b.property
    · have he := D.line_eq_of_mem (f.i_ne_affine b.val.val) hx (f.i_ne_affine x.val)
      exact he.symm ▸ D.right_mem_line f.i (b : Ω)
  · intro he
    have hx : (x : Ω) ∈ D.line f.i ((f.second hline hq x).val : Ω) := by
      change (x : Ω) ∈ D.line f.i (f.cross hline hq (f.baseOrigin hline hq) x : Ω)
      rw [f.cross_right_line]
      exact D.right_mem_line _ _
    simpa only [he] using hx

theorem height_fiber (x : f.Affine) (z : f.Axis) :
    (x : Ω) ∈ D.block (f.level hline hq z.val) ↔ f.height hline hq x = z := by
  constructor
  · intro hx
    apply Subtype.ext
    apply Subtype.ext
    refine D.project_eq hline hq _ _ (f.k_not_level hline hq x) _
      (f.k_ne_affine f.originPoint) z.property ?_
    rw [f.level_eq_of_mem hline hq z.val x hx]
    exact (f.level_spec hline hq z.val).2.2
  · intro he
    have hh := f.height_level hline hq x
    rw [he] at hh
    rw [hh]
    exact (f.level_spec hline hq x).2.2

include hline in
theorem axisAt_card (d : Ω) (hd : d ∈ D.block f.infinity) : Nat.card (f.AxisAt d) = q := by
  have hdo : d ≠ f.origin := fun he => f.origin_not_mem (he ▸ hd)
  let e : f.AxisAt d ≃ ↥(D.line d f.origin \ {d}) :=
    { toFun := fun x => ⟨x,x.property,fun he =>
        x.val.property ((show (x : Ω) = d from he).symm ▸ hd)⟩
      invFun := fun x => ⟨⟨x,fun hx => x.property.2
        ((D.infinity_on_line hd f.origin_not_mem x.property.1).mp hx)⟩,x.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  change (D.line d f.origin \ {d}).ncard = q
  rw [Set.ncard_sdiff_singleton_of_mem (D.left_mem_line d f.origin),hline d f.origin hdo]
  omega

@[expose] def axisIEquiv : f.AxisI hline hq ≃ f.AxisAt f.i where
  toFun x := ⟨x.val.val,x.property⟩
  invFun x := ⟨⟨x.val,D.line_subset_block (f.level_spec hline hq f.originPoint).1
    (f.level_spec hline hq f.originPoint).2.2 x.property⟩,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[expose] def axisJEquiv : f.AxisJ hline hq ≃ f.AxisAt f.j where
  toFun x := ⟨x.val.val,x.property⟩
  invFun x := ⟨⟨x.val,D.line_subset_block (f.level_spec hline hq f.originPoint).2.1
    (f.level_spec hline hq f.originPoint).2.2 x.property⟩,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- All three coordinate axes have the source field cardinality. -/
theorem axes_card : Nat.card (f.AxisI hline hq) = q ∧
    Nat.card (f.AxisJ hline hq) = q ∧ Nat.card f.Axis = q :=
  ⟨(Nat.card_congr (f.axisIEquiv hline hq)).trans (f.axisAt_card hline f.i f.i_mem),
    (Nat.card_congr (f.axisJEquiv hline hq)).trans (f.axisAt_card hline f.j f.j_mem),
    f.axisAt_card hline f.k f.k_mem⟩

include hline hq in
/-- The constructed chart has q³ points; no choice of field arithmetic is
used in the chart or in this count. -/
theorem affine_card : Nat.card f.Affine = q^3 := by
  rw [Nat.card_congr (f.axisCoordinates hline hq),Nat.card_prod,Nat.card_prod,
    (f.axes_card hline hq).1,(f.axes_card hline hq).2.1,(f.axes_card hline hq).2.2]
  simp [pow_succ]

end AffineFrame
end Theory.GroupAction.SymplecticRankThree
