module
public import Mathlib.Combinatorics.Configuration

/-!
# Collineations and uniqueness of an elation centre

A collineation action preserves incidence between the given points and lines.
An elation fixes its axis pointwise and every line through its centre, which
lies on the axis. Nontriviality means that some point or line moves; neither
group action is assumed faithful. In a finite projective plane, two elation
witnesses for the same group element and axis have the same centre.

This is the elementary uniqueness fact in Wagner, *On perspectivities of
finite projective planes*, Section 2, article page 114. It supplies the
centre-injectivity step in the finite counting argument of his Theorem 1,
used toward recognition of a finite plane from its elations.

If two centres were distinct, a point off the axis would be the unique
intersection of its two fixed joining lines to the centres, so every point
would be fixed. Every line contains two distinct points, and incidence
preservation and line uniqueness would then fix every line as well. This
contradicts the movement required of an elation.
-/

namespace Configuration

/-- A group action on points and lines is by collineations when the two actions
preserve the given incidence relation. -/
public class IsCollineationAction (H P L : Type*) [Group H] [Membership P L]
    [MulAction H P] [MulAction H L] : Prop where
  smul_mem_smul_iff (g : H) (p : P) (l : L) : g • p ∈ g • l ↔ p ∈ l

/-- An elation fixes its axis pointwise and the pencil through its incident
centre, and acts nontrivially on the underlying point-line configuration. -/
public structure IsElation {H P L : Type*} [Group H] [Membership P L]
    [MulAction H P] [MulAction H L] (g : H) (C : P) (l : L) : Prop where
  incident : C ∈ l
  fixes_axis_points : ∀ p : P, p ∈ l → g • p = p
  fixes_center_lines : ∀ m : L, C ∈ m → g • m = m
  moves : (∃ p : P, g • p ≠ p) ∨ ∃ m : L, g • m ≠ m

namespace IsElation

variable {H P L : Type*} [Group H] [Membership P L]
  [MulAction H P] [MulAction H L] [IsCollineationAction H P L]
  [Finite P] [Finite L] [ProjectivePlane P L]

/-- A nontrivial elation has a unique centre once its axis is fixed. -/
public theorem center_eq {g : H} {C D : P} {l : L}
    (hC : IsElation g C l) (hD : IsElation g D l) : C = D := by
  by_contra hCD
  have hpoint : ∀ q : P, g • q = q := by
    intro q
    by_cases hql : q ∈ l
    · exact hC.fixes_axis_points q hql
    · have hqC : q ≠ C := by
        intro h
        apply hql
        rw [h]
        exact hC.incident
      have hqD : q ≠ D := by
        intro h
        apply hql
        rw [h]
        exact hD.incident
      let mC : L := HasLines.mkLine hqC
      let mD : L := HasLines.mkLine hqD
      have hq_mC : q ∈ mC := (HasLines.mkLine_ax hqC).1
      have hC_mC : C ∈ mC := (HasLines.mkLine_ax hqC).2
      have hq_mD : q ∈ mD := (HasLines.mkLine_ax hqD).1
      have hD_mD : D ∈ mD := (HasLines.mkLine_ax hqD).2
      have hmCD : mC ≠ mD := by
        intro hm
        have hD_mC : D ∈ mC := by simpa only [hm] using hD_mD
        rcases Nondegenerate.eq_or_eq hC.incident hD.incident hC_mC hD_mC with h | h
        · exact hCD h
        · exact hql ((congrArg (q ∈ ·) h).mpr hq_mC)
      have hg_mC : g • mC = mC := hC.fixes_center_lines mC hC_mC
      have hg_mD : g • mD = mD := hD.fixes_center_lines mD hD_mD
      have hgq_mC : g • q ∈ mC := by
        have h := (IsCollineationAction.smul_mem_smul_iff g q mC).2 hq_mC
        rwa [hg_mC] at h
      have hgq_mD : g • q ∈ mD := by
        have h := (IsCollineationAction.smul_mem_smul_iff g q mD).2 hq_mD
        rwa [hg_mD] at h
      exact (Nondegenerate.eq_or_eq hgq_mC hq_mC hgq_mD hq_mD).resolve_right hmCD
  have hline : ∀ m : L, g • m = m := by
    intro m
    let : Fintype P := Fintype.ofFinite P
    let : Fintype L := Fintype.ofFinite L
    let : Fintype {p : P // p ∈ m} := Fintype.ofFinite _
    have hcard : 1 < Fintype.card {p : P // p ∈ m} := by
      rw [← Nat.card_eq_fintype_card]
      change 1 < pointCount P m
      exact lt_trans (by omega) (ProjectivePlane.two_lt_pointCount P m)
    obtain ⟨p, q, hpq⟩ := Fintype.one_lt_card_iff.mp hcard
    have hp_gm : (p : P) ∈ g • m := by
      have h := (IsCollineationAction.smul_mem_smul_iff g (p : P) m).2 p.property
      rwa [hpoint] at h
    have hq_gm : (q : P) ∈ g • m := by
      have h := (IsCollineationAction.smul_mem_smul_iff g (q : P) m).2 q.property
      rwa [hpoint] at h
    exact (Nondegenerate.eq_or_eq p.property q.property hp_gm hq_gm).resolve_left
      (fun h => hpq (Subtype.ext h)) |>.symm
  rcases hC.moves with hmove | hmove
  · obtain ⟨p, hp⟩ := hmove
    exact hp (hpoint p)
  · obtain ⟨m, hm⟩ := hmove
    exact hm (hline m)

end IsElation

end Configuration
