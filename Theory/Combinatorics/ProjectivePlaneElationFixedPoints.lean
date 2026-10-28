module
public import Theory.Combinatorics.ProjectivePlaneCollineation

/-!
# Fixed points of an elation

In a finite projective plane, a nontrivial elation moves every point off its
axis. This is the elation case of Wagner, *On perspectivities of finite
projective planes*, Section 2, article page 114: the only fixed points of a
perspectivity are its center and axis points. It supplies the fixed-point
input for semiregular translation and root actions in finite-plane recognition.

Suppose an off-axis point is fixed. Every line through it is then fixed,
since its intersection with the axis is a second fixed point. Intersecting
these lines with the fixed center pencil fixes all points outside the line
joining that point to the center. Any other axis point is consequently a
second elation center: each line through it contains a fixed point outside
both exceptional lines. The fact that each line has more than two points
supplies these choices. Center uniqueness gives the contradiction.

The result uses the original incidence and collineation actions and the
movement-based `IsElation`; it assumes neither faithful actions nor coordinates.
-/

namespace Configuration

variable {H P L : Type*} [Group H] [Membership P L]
  [MulAction H P] [MulAction H L] [IsCollineationAction H P L]
  [Finite P] [Finite L] [ProjectivePlane P L]

private theorem exists_point_on_line_avoiding_two_lines
    (m l n : L) (hml : m ≠ l) (hmn : m ≠ n) :
    ∃ q : P, q ∈ m ∧ q ∉ l ∧ q ∉ n := by
  classical
  let : Fintype {q : P // q ∈ m} := Fintype.ofFinite _
  have hcard : 2 < Fintype.card {q : P // q ∈ m} := by
    rw [← Nat.card_eq_fintype_card]
    exact ProjectivePlane.two_lt_pointCount P m
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hcard
  by_contra h
  have hcover (q : {q : P // q ∈ m}) : (q : P) ∈ l ∨ (q : P) ∈ n := by
    by_cases hq : (q : P) ∈ l
    · exact Or.inl hq
    · exact Or.inr (not_not.mp (fun hn => h ⟨q, q.property, hq, hn⟩))
  have hpair (x y : {q : P // q ∈ m}) (hxy : x ≠ y)
      (k : L) (hmk : m ≠ k) (hx : (x : P) ∈ k) (hy : (y : P) ∈ k) : False := by
    exact ((Nondegenerate.eq_or_eq x.property y.property hx hy).elim
      (fun h => hxy (Subtype.ext h)) hmk)
  rcases hcover a with ha | ha <;> rcases hcover b with hb | hb <;>
    rcases hcover c with hc | hc
  all_goals first
    | exact hpair a b hab l hml ha hb
    | exact hpair a c hac l hml ha hc
    | exact hpair b c hbc l hml hb hc
    | exact hpair a b hab n hmn ha hb
    | exact hpair a c hac n hmn ha hc
    | exact hpair b c hbc n hmn hb hc

omit [Finite P] [Finite L] in
private theorem line_fixed_of_two_fixed_points {g : H} {p q : P} {m : L}
    (hpq : p ≠ q) (hp : p ∈ m) (hq : q ∈ m)
    (hgp : g • p = p) (hgq : g • q = q) : g • m = m := by
  have hp' := (IsCollineationAction.smul_mem_smul_iff g p m).mpr hp
  have hq' := (IsCollineationAction.smul_mem_smul_iff g q m).mpr hq
  rw [hgp] at hp'
  rw [hgq] at hq'
  exact ((Nondegenerate.eq_or_eq hp hq hp' hq').resolve_left hpq).symm

omit [Finite P] [Finite L] in
private theorem lines_through_fixed_off_axis_point {g : H} {C p : P} {l : L}
    (h : IsElation g C l) (hpl : p ∉ l) (hp : g • p = p)
    (m : L) (hpm : p ∈ m) : g • m = m := by
  have hml : m ≠ l := by rintro rfl; exact hpl hpm
  let q : P := HasPoints.mkPoint hml
  have hqm : q ∈ m := (HasPoints.mkPoint_ax hml).1
  have hql : q ∈ l := (HasPoints.mkPoint_ax hml).2
  exact line_fixed_of_two_fixed_points (ne_of_mem_of_not_mem hql hpl)
    hqm hpm (h.fixes_axis_points q hql) hp

public theorem IsElation.smul_ne_of_not_mem_axis {g : H} {C p : P} {l : L}
    (h : IsElation g C l) (hpl : p ∉ l) : g • p ≠ p := by
  intro hp
  have hpC : p ≠ C := fun heq => hpl (heq ▸ h.incident)
  let n : L := HasLines.mkLine hpC
  have hpn : p ∈ n := (HasLines.mkLine_ax hpC).1
  have hCn : C ∈ n := (HasLines.mkLine_ax hpC).2
  have hnl : n ≠ l := by rintro hnl; exact hpl (hnl ▸ hpn)
  have hfix (q : P) (hqn : q ∉ n) : g • q = q := by
    have hqC : q ≠ C := fun heq => hqn (heq ▸ hCn)
    have hqp : q ≠ p := fun heq => hqn (heq ▸ hpn)
    let mC : L := HasLines.mkLine hqC
    let mp : L := HasLines.mkLine hqp
    have hqC' : q ∈ mC := (HasLines.mkLine_ax hqC).1
    have hCC : C ∈ mC := (HasLines.mkLine_ax hqC).2
    have hqp' : q ∈ mp := (HasLines.mkLine_ax hqp).1
    have hpp : p ∈ mp := (HasLines.mkLine_ax hqp).2
    have hne : mC ≠ mp := by
      intro heq
      have hpmC : p ∈ mC := heq.symm ▸ hpp
      have hmCn : mC = n :=
        (Nondegenerate.eq_or_eq hpmC hCC hpn hCn).resolve_left hpC
      exact hqn (hmCn ▸ hqC')
    have hgC := h.fixes_center_lines mC hCC
    have hgp := lines_through_fixed_off_axis_point h hpl hp mp hpp
    have hgqC := (IsCollineationAction.smul_mem_smul_iff g q mC).mpr hqC'
    have hgqp := (IsCollineationAction.smul_mem_smul_iff g q mp).mpr hqp'
    rw [hgC] at hgqC
    rw [hgp] at hgqp
    exact (Nondegenerate.eq_or_eq hgqC hqC' hgqp hqp').resolve_right hne
  obtain ⟨D, hDl, hDn, _⟩ :=
    exists_point_on_line_avoiding_two_lines (P := P) l n n hnl.symm hnl.symm
  have hDC : D ≠ C := fun heq => hDn (heq ▸ hCn)
  have hD : IsElation g D l := by
    refine ⟨hDl, h.fixes_axis_points, ?_, h.moves⟩
    intro m hDm
    by_cases hml : m = l
    · exact hml ▸ h.fixes_center_lines l h.incident
    have hmn : m ≠ n := by rintro rfl; exact hDn hDm
    obtain ⟨q, hqm, hql, hqn⟩ :=
      exists_point_on_line_avoiding_two_lines (P := P) m l n hml hmn
    exact line_fixed_of_two_fixed_points (ne_of_mem_of_not_mem hDl hql)
      hDm hqm (h.fixes_axis_points D hDl) (hfix q hqn)
  exact hDC (hD.center_eq h)

end Configuration
