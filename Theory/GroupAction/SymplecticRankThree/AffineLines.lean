module
public import Theory.GroupAction.SymplecticRankThree.AffineChart

/-!
# Line graphs in the reconstructed affine chart

Two distinct points at infinity give parallel pencils. Every pair of their
lines meets in exactly one affine point. Thus a nonvertical line is the
graph of a function between the two actual affine axes. Horizontal lines
are constant graphs, and every other direction gives a bijection. Every
affine line in the base plane has one of these equations, including q=2.
A diagonal identifies the two axes geometrically and has equation x=y in
the resulting common scalar alphabet.

This is the geometric input to field coordinatization. The graph functions
are constructed by incidence; this module does not assert that they have
the field-linear form mx+b. That arithmetic conclusion remains necessary
for the nonbinary projective recognition.

Source: Higman (1964), Lemma 10, pp.153–154, the projective coordinatization
step expanded using parallel pencils. The actual source application is
FongSeitzBinary.SymplecticRankThree.SourceAffine.
-/

public noncomputable section
namespace Theory.GroupAction.SymplecticRankThree.AffineFrame
variable {Ω : Type*} [Finite Ω] {q : ℕ} {D : PolarityDesign Ω q}
variable (f : AffineFrame D)
variable (hline : ∀ a b, a ≠ b → (D.line a b).ncard = q+1) (hq : 2 ≤ q)

abbrev Direction := {d : Ω // d ∈ D.block f.infinity ∧
  d ∈ D.block (f.level hline hq f.originPoint)}

@[expose] def directionI : f.Direction hline hq :=
  ⟨f.i,f.i_mem,(f.level_spec hline hq f.originPoint).1⟩

@[expose] def directionJ : f.Direction hline hq :=
  ⟨f.j,f.j_mem,(f.level_spec hline hq f.originPoint).2.1⟩

theorem direction_ne_affine (d : f.Direction hline hq) (x : f.Affine) : (d : Ω) ≠ x :=
  fun he => x.property (he ▸ d.property.1)

theorem meet_existsUnique (d e : f.Direction hline hq) (hde : (d : Ω) ≠ e)
    (a b : f.Base hline hq) :
    ∃! x : Ω, x ∈ D.line d (a : Ω) ∧ x ∈ D.line e (b : Ω) := by
  obtain ⟨x,hxa,hxb⟩ := D.coplanar_lines_meet hline (f.direction_ne_affine hline hq d a.val)
    (f.direction_ne_affine hline hq e b.val) d.property.2 a.property e.property.2 b.property
  refine ⟨x,⟨hxa,hxb⟩,?_⟩
  intro y hy
  by_contra hne
  have he : D.line d (a : Ω) = D.line e (b : Ω) :=
    (D.line_eq_of_mem_of_mem (f.direction_ne_affine hline hq d a.val) hy.1 hxa hne).symm.trans
      (D.line_eq_of_mem_of_mem (f.direction_ne_affine hline hq e b.val) hy.2 hxb hne)
  have hd : (d : Ω) ∈ D.line e (b : Ω) := he ▸ D.left_mem_line d (a : Ω)
  exact hde ((D.infinity_on_line e.property.1 b.val.property hd).mp d.property.1)

@[expose] def meet (d e : f.Direction hline hq) (hde : (d : Ω) ≠ e)
    (a b : f.Base hline hq) : f.Base hline hq := by
  let x := (f.meet_existsUnique hline hq d e hde a b).choose
  have hxl : x ∈ D.line d (a : Ω) := (f.meet_existsUnique hline hq d e hde a b).choose_spec.1.1
  have hxr : x ∈ D.line e (b : Ω) := (f.meet_existsUnique hline hq d e hde a b).choose_spec.1.2
  have hx : x ∉ D.block f.infinity := by
    intro hx
    have hxd := (D.infinity_on_line d.property.1 a.val.property hxl).mp hx
    have hxe := (D.infinity_on_line e.property.1 b.val.property hxr).mp hx
    exact hde (hxd.symm.trans hxe)
  exact ⟨⟨x,hx⟩,D.line_subset_block d.property.2 a.property hxl⟩

theorem meet_mem_left (d e : f.Direction hline hq) (hde : (d : Ω) ≠ e)
    (a b : f.Base hline hq) :
    (f.meet hline hq d e hde a b : Ω) ∈ D.line d (a : Ω) :=
  (f.meet_existsUnique hline hq d e hde a b).choose_spec.1.1

theorem meet_mem_right (d e : f.Direction hline hq) (hde : (d : Ω) ≠ e)
    (a b : f.Base hline hq) :
    (f.meet hline hq d e hde a b : Ω) ∈ D.line e (b : Ω) :=
  (f.meet_existsUnique hline hq d e hde a b).choose_spec.1.2

theorem meet_eq (d e : f.Direction hline hq) (hde : (d : Ω) ≠ e)
    (a b x : f.Base hline hq)
    (hl : (x : Ω) ∈ D.line d (a : Ω)) (hr : (x : Ω) ∈ D.line e (b : Ω)) :
    f.meet hline hq d e hde a b = x :=
  Subtype.ext (Subtype.ext ((f.meet_existsUnique hline hq d e hde a b).choose_spec.2 x ⟨hl,hr⟩).symm)

@[expose] def graphPoint (d : f.Direction hline hq) (hd : (d : Ω) ≠ f.j)
    (b : f.AxisJ hline hq) (a : f.AxisI hline hq) : f.Base hline hq :=
  f.meet hline hq (f.directionJ hline hq) d hd.symm a.val b.val

theorem graphPoint_first (d : f.Direction hline hq) (hd : (d : Ω) ≠ f.j)
    (b : f.AxisJ hline hq) (a : f.AxisI hline hq) :
    f.first hline hq (f.graphPoint hline hq d hd b a) = a :=
  (f.first_fiber hline hq _ a).mp
    (f.meet_mem_left hline hq (f.directionJ hline hq) d hd.symm a.val b.val)

@[expose] def graphValue (d : f.Direction hline hq) (hd : (d : Ω) ≠ f.j)
    (b : f.AxisJ hline hq) (a : f.AxisI hline hq) : f.AxisJ hline hq :=
  f.second hline hq (f.graphPoint hline hq d hd b a)

/-- Every line with nonvertical direction is the graph of a function in
the Cartesian chart. This asserts no field formula for that function. -/
theorem graph_incidence (d : f.Direction hline hq) (hd : (d : Ω) ≠ f.j)
    (b : f.AxisJ hline hq) (x : f.Base hline hq) :
    (x : Ω) ∈ D.line d (b : Ω) ↔
      f.second hline hq x = f.graphValue hline hq d hd b (f.first hline hq x) := by
  constructor
  · intro hx
    have he : f.graphPoint hline hq d hd b (f.first hline hq x) = x :=
      f.meet_eq hline hq (f.directionJ hline hq) d hd.symm _ _ x
        ((f.first_fiber hline hq x (f.first hline hq x)).mpr rfl) hx
    exact (congrArg (f.second hline hq) he).symm
  · intro hx
    have he : x = f.graphPoint hline hq d hd b (f.first hline hq x) := by
      apply (f.baseEquiv hline hq).injective
      exact Prod.ext (f.graphPoint_first hline hq d hd b _).symm hx
    rw [he]
    exact f.meet_mem_right hline hq (f.directionJ hline hq) d hd.symm _ _

/-- Every direction other than either coordinate direction gives a
permutation between the two affine axes. -/
theorem graphValue_bijective (d : f.Direction hline hq) (hd : (d : Ω) ≠ f.j)
    (hi : (d : Ω) ≠ f.i) (b : f.AxisJ hline hq) :
    Function.Bijective (f.graphValue hline hq d hd b) := by
  constructor
  · intro a a' he
    let x := f.graphPoint hline hq d hd b a
    let y := f.graphPoint hline hq d hd b a'
    have hx : (x : Ω) ∈ D.line f.i (f.graphValue hline hq d hd b a : Ω) :=
      (f.second_fiber hline hq x _).mpr rfl
    have hy : (y : Ω) ∈ D.line f.i (f.graphValue hline hq d hd b a : Ω) := by
      rw [he]
      exact (f.second_fiber hline hq y _).mpr rfl
    have ex := f.meet_eq hline hq (f.directionI hline hq) d hi.symm
      (f.graphValue hline hq d hd b a).val b.val x hx
      (f.meet_mem_right hline hq (f.directionJ hline hq) d hd.symm a.val b.val)
    have ey := f.meet_eq hline hq (f.directionI hline hq) d hi.symm
      (f.graphValue hline hq d hd b a).val b.val y hy
      (f.meet_mem_right hline hq (f.directionJ hline hq) d hd.symm a'.val b.val)
    have hh := congrArg (f.first hline hq) (ex.symm.trans ey)
    simpa only [x,y,graphPoint_first] using hh
  · intro z
    let x := f.meet hline hq (f.directionI hline hq) d hi.symm z.val b.val
    have hz : f.second hline hq x = z := (f.second_fiber hline hq x z).mp
      (f.meet_mem_left hline hq (f.directionI hline hq) d hi.symm z.val b.val)
    have hx := (f.graph_incidence hline hq d hd b x).mp
      (f.meet_mem_right hline hq (f.directionI hline hq) d hi.symm z.val b.val)
    exact ⟨f.first hline hq x,hx.symm.trans hz⟩

/-- A horizontal line has constant second coordinate. -/
theorem horizontal_graph (b : f.AxisJ hline hq) (a : f.AxisI hline hq) :
    f.graphValue hline hq (f.directionI hline hq) f.ij_ne b a = b :=
  (f.second_fiber hline hq _ b).mp
    (f.meet_mem_right hline hq (f.directionJ hline hq) (f.directionI hline hq)
      f.ij_ne.symm a.val b.val)

theorem nonvertical_line_graph (a b : f.Base hline hq) (hab : (a : Ω) ≠ (b : Ω))
    (hv : f.j ∉ D.line (a : Ω) (b : Ω)) :
    ∃ (d : f.Direction hline hq) (hd : (d : Ω) ≠ f.j) (c : f.AxisJ hline hq),
      ∀ x : f.Base hline hq, (x : Ω) ∈ D.line (a : Ω) (b : Ω) ↔
        f.second hline hq x = f.graphValue hline hq d hd c (f.first hline hq x) := by
  obtain ⟨d,⟨hdl,hdp⟩,_⟩ := D.existsUnique_line_block hline hq a.val.property hab
  let d' : f.Direction hline hq := ⟨d,hdp,D.line_subset_block a.property b.property hdl⟩
  have hdj : (d' : Ω) ≠ f.j := fun he => hv (he ▸ hdl)
  let y := f.meet hline hq d' (f.directionJ hline hq) hdj a (f.baseOrigin hline hq)
  let c : f.AxisJ hline hq := ⟨y,f.meet_mem_right hline hq d' (f.directionJ hline hq)
    hdj a (f.baseOrigin hline hq)⟩
  have hda : d ≠ (a : Ω) := f.direction_ne_affine hline hq d' a.val
  have hlinea : D.line d (a : Ω) = D.line (a : Ω) (b : Ω) :=
    (D.line_comm d (a : Ω)).trans (D.line_eq_of_mem hab hdl hda.symm)
  have hy : (c : Ω) ∈ D.line (a : Ω) (b : Ω) := hlinea ▸
    f.meet_mem_left hline hq d' (f.directionJ hline hq) hdj a (f.baseOrigin hline hq)
  have he : D.line d (c : Ω) = D.line (a : Ω) (b : Ω) :=
    D.line_eq_of_mem_of_mem hab hdl hy (f.direction_ne_affine hline hq d' c.val.val)
  refine ⟨d',hdj,c,?_⟩
  intro x
  rw [← he]
  exact f.graph_incidence hline hq d' hdj c x

/-- Exhaustive equations for affine lines: constant first coordinate or
the graph belonging to a direction and an intercept. -/
theorem line_equations (a b : f.Base hline hq) (hab : (a : Ω) ≠ (b : Ω)) :
    (∃ c : f.AxisI hline hq, ∀ x : f.Base hline hq,
      (x : Ω) ∈ D.line (a : Ω) (b : Ω) ↔ f.first hline hq x = c) ∨
    (∃ (d : f.Direction hline hq) (hd : (d : Ω) ≠ f.j) (c : f.AxisJ hline hq),
      ∀ x : f.Base hline hq, (x : Ω) ∈ D.line (a : Ω) (b : Ω) ↔
        f.second hline hq x = f.graphValue hline hq d hd c (f.first hline hq x)) := by
  by_cases hv : f.j ∈ D.line (a : Ω) (b : Ω)
  · left
    refine ⟨f.first hline hq a,?_⟩
    have hja : D.line f.j (a : Ω) = D.line (a : Ω) (b : Ω) :=
      D.line_eq_of_mem_of_mem hab hv (D.left_mem_line _ _) (f.j_ne_affine a.val)
    have hfa : D.line f.j (f.first hline hq a : Ω) = D.line f.j (a : Ω) :=
      f.cross_left_line hline hq a (f.baseOrigin hline hq)
    intro x
    rw [← hja,← hfa]
    exact f.first_fiber hline hq x _
  · exact Or.inr (f.nonvertical_line_graph hline hq a b hab hv)

/-- The line at infinity has a direction distinct from both coordinate
directions, also when q=2. -/
theorem exists_diagonal_direction :
    ∃ d : f.Direction hline hq, (d : Ω) ≠ f.i ∧ (d : Ω) ≠ f.j := by
  have hnot : ¬ D.line f.i f.j ⊆ {f.i,f.j} := by
    intro hh
    have hc := Set.ncard_le_ncard hh
    rw [hline f.i f.j f.ij_ne,Set.ncard_pair f.ij_ne] at hc
    omega
  obtain ⟨d,hd,hdn⟩ := Set.not_subset.mp hnot
  refine ⟨⟨d,D.line_subset_block f.i_mem f.j_mem hd,
    D.line_subset_block (f.level_spec hline hq f.originPoint).1
      (f.level_spec hline hq f.originPoint).2.1 hd⟩,?_,?_⟩
  · exact fun he => hdn (Or.inl he)
  · exact fun he => hdn (Or.inr he)

@[expose] def originJ : f.AxisJ hline hq :=
  ⟨f.baseOrigin hline hq,D.right_mem_line f.j f.origin⟩

/-- A diagonal line through the origin identifies the two affine axes
geometrically. No arbitrary enumeration of their points is used. -/
@[expose] def diagonalEquiv (d : f.Direction hline hq)
    (hi : (d : Ω) ≠ f.i) (hj : (d : Ω) ≠ f.j) : f.AxisI hline hq ≃ f.AxisJ hline hq :=
  Equiv.ofBijective (f.graphValue hline hq d hj (f.originJ hline hq))
    (f.graphValue_bijective hline hq d hj hi (f.originJ hline hq))

/-- The two planar coordinates now use the same scalar alphabet. The
field operations on that alphabet are still to be constructed. -/
@[expose] def scalarCoordinates (d : f.Direction hline hq)
    (hi : (d : Ω) ≠ f.i) (hj : (d : Ω) ≠ f.j) :
    f.Base hline hq ≃ f.AxisI hline hq × f.AxisI hline hq :=
  (f.baseEquiv hline hq).trans
    ((Equiv.refl _).prodCongr (f.diagonalEquiv hline hq d hi hj).symm)

/-- The chosen geometric diagonal has the literal equation x=y in the
single-alphabet coordinates. -/
theorem scalarCoordinates_diagonal (d : f.Direction hline hq)
    (hi : (d : Ω) ≠ f.i) (hj : (d : Ω) ≠ f.j) (x : f.Base hline hq) :
    (x : Ω) ∈ D.line d f.origin ↔
      (f.scalarCoordinates hline hq d hi hj x).1 = (f.scalarCoordinates hline hq d hi hj x).2 := by
  let E := f.diagonalEquiv hline hq d hi hj
  change (x : Ω) ∈ D.line d f.origin ↔ f.first hline hq x = E.symm (f.second hline hq x)
  have hh := f.graph_incidence hline hq d hj (f.originJ hline hq) x
  change (x : Ω) ∈ D.line d f.origin ↔ f.second hline hq x = E (f.first hline hq x) at hh
  rw [hh]
  change f.second hline hq x = E (f.first hline hq x) ↔
    f.first hline hq x = E.symm (f.second hline hq x)
  constructor
  · intro he
    apply E.injective
    rw [E.apply_symm_apply]
    exact he.symm
  · intro he
    have hh := congrArg E he
    simpa only [E.apply_symm_apply] using hh.symm

end Theory.GroupAction.SymplecticRankThree.AffineFrame
