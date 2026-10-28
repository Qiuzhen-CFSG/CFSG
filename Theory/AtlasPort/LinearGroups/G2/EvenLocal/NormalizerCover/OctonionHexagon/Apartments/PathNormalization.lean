module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Uses the coordinate reductions from the ATLAS port, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: derive the nonzero coordinates from intrinsic incidence and compose
actual octonion automorphisms to normalize four consecutive hexagon points.
-/

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Apartments.Configurations
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Apartments.CoordinateCalculations
public import Theory.AtlasPort.LinearGroups.G2.PointOrbits

/-!
# Normalizing four consecutive octonion hexagon points

Every point hexagon can be moved so that its first four points are the lines
of basis vectors 0, 1, 5, and 7. Point transitivity normalizes the first point;
the parabolic lower-vector reduction normalizes the second while fixing it.
The annihilator calculations then put the third and fourth representatives
in the domains of the explicit root reducers.

The required denominators are nonzero because otherwise the new point lies
on the preceding line. Two distinct points determine a unique zero-product
plane, so that would identify two of the hexagon's distinct lines. This
argument works over every field.

Source context: the split G₂ case of Aschbacher--Smith, Theorem 0.1.2(1),
printed pp.3--4, repeated as Theorem 0.1.1, printed pp.481--482. This is a
geometric normalization ingredient; the complete twelve-cycle theorem is
assembled separately in Apartments.lean.
-/

public section

open Atlas.G2 Atlas.SplitOctonion
open scoped LinearAlgebra.Projectivization
namespace Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.Apartments
variable {F : Type*} [Field F]

private theorem smul_point_eq_coordinate (g : Model F) (p : SingularPoints F)
    (i : Fin 6) (a : F) (h : g.val p.val.rep = a • offDiagonalVector i) :
    g • p = coordinatePoint i := by
  rw [← singularPointMk_rep F p, singularPointMk_smul, coordinatePoint]
  apply Subtype.ext
  apply (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr
  exact ⟨a, h.symm⟩

private theorem point_eq_coordinate (p : SingularPoints F) (i : Fin 6) (a : F)
    (h : p.val.rep = a • offDiagonalVector i) : p = coordinatePoint i := by
  simpa only [one_smul] using smul_point_eq_coordinate (1 : Model F) p i a h

private theorem fixed_of_vector (g : Model F) (i : Fin 6)
    (h : g.val (offDiagonalVector i) = offDiagonalVector i) :
    g • coordinatePoint (F := F) i = coordinatePoint i := by
  apply (coordinatePoint_fixed_iff g i).mpr
  exact ⟨1, by simpa only [Units.val_one, one_smul] using h⟩

private theorem third_not_on_first (H : PointHexagon F) :
    ¬ pointOnLine (H.point 2) (H.line 0) := by
  intro h
  have he : H.line 0 = H.line 1 := line_eq_of_points
    (fun he => (by decide : (1 : Fin 6) ≠ 2) (H.point_injective he))
    (H.next_on 0) h (H.point_on 1) (H.next_on 1)
  exact (by decide : (0 : Fin 6) ≠ 1) (H.line_injective he)

private theorem fourth_not_on_second (H : PointHexagon F) :
    ¬ pointOnLine (H.point 3) (H.line 1) := by
  intro h
  have he : H.line 1 = H.line 2 := line_eq_of_points
    (fun he => (by decide : (2 : Fin 6) ≠ 3) (H.point_injective he))
    (H.next_on 1) h (H.point_on 2) (H.next_on 2)
  exact (by decide : (1 : Fin 6) ≠ 2) (H.line_injective he)

private theorem normalize_second (H : PointHexagon F)
    (h0 : H.point 0 = coordinatePoint 0) :
    ∃ g : Model F, (H.map g).point 0 = coordinatePoint 0 ∧
      (H.map g).point 1 = coordinatePoint 1 := by
  let x := (H.point 1).val.rep
  have hx : x = ![x 0,x 1,x 2,0,0,0,0,0] :=
    annihilator_basis_zero x (products_zero_of_coordinate_on 0
      (h0 ▸ H.point_on 0) (H.next_on 0))
  have hpair : x 1 ≠ 0 ∨ x 2 ≠ 0 := by
    by_contra hpair
    push Not at hpair
    have he : x = x 0 • offDiagonalVector 0 := by
      calc
        x = ![x 0,x 1,x 2,0,0,0,0,0] := hx
        _ = x 0 • offDiagonalVector 0 := by
          ext i
          fin_cases i <;> simp [offDiagonalVector, offDiagonalIndex, basisVector,
            hpair.1, hpair.2]
    have hp : H.point 1 = H.point 0 := (point_eq_coordinate _ 0 (x 0) he).trans h0.symm
    exact (by decide : (1 : Fin 6) ≠ 0) (H.point_injective hp)
  obtain ⟨g,hg,a,_ha,he⟩ := lower_vector_reduction x (H.point 1).property.1
    (H.point 1).property.2 (congrFun hx 5) (congrFun hx 6) (congrFun hx 7) hpair
  refine ⟨g, ?_, smul_point_eq_coordinate g (H.point 1) 1 a he⟩
  rw [PointHexagon.map_point, h0]
  exact (show g • firstPoint = firstPoint from parabolic_le_pointStabilizer hg)

private theorem normalize_third (H : PointHexagon F)
    (h0 : H.point 0 = coordinatePoint 0) (h1 : H.point 1 = coordinatePoint 1) :
    ∃ g : Model F, (H.map g).point 0 = coordinatePoint 0 ∧
      (H.map g).point 1 = coordinatePoint 1 ∧
      (H.map g).point 2 = coordinatePoint 3 := by
  let x := (H.point 2).val.rep
  have hx : x = ![x 0,x 1,0,0,0,x 5,0,0] :=
    annihilator_basis_one x (products_zero_of_coordinate_on 1
      (h1 ▸ H.point_on 1) (H.next_on 1))
  have h5 : x 5 ≠ 0 := by
    intro h5
    apply third_not_on_first H
    apply (pointOnLine_iff _ _).mpr
    have he : x = x 0 • offDiagonalVector 0 + x 1 • offDiagonalVector 1 := by
      calc
        x = ![x 0,x 1,0,0,0,x 5,0,0] := hx
        _ = x 0 • offDiagonalVector 0 + x 1 • offDiagonalVector 1 := by
          ext i
          fin_cases i <;> simp [offDiagonalVector, offDiagonalIndex, basisVector, h5]
    change x ∈ (H.line 0).val
    rw [he]
    exact (H.line 0).val.add_mem
      ((H.line 0).val.smul_mem (x 0) ((coordinatePoint_on_iff 0 _).mp (h0 ▸ H.point_on 0)))
      ((H.line 0).val.smul_mem (x 1) ((coordinatePoint_on_iff 1 _).mp (h1 ▸ H.next_on 0)))
  refine ⟨thirdReducer x, ?_, ?_, ?_⟩
  · rw [PointHexagon.map_point, h0]
    exact fixed_of_vector _ 0 (thirdReducer_fixes x).1
  · rw [PointHexagon.map_point, h1]
    exact fixed_of_vector _ 1 (thirdReducer_fixes x).2
  · exact smul_point_eq_coordinate _ (H.point 2) 3 (x 5) (thirdReducer_apply x hx h5)

private theorem normalize_fourth (H : PointHexagon F)
    (h0 : H.point 0 = coordinatePoint 0) (h1 : H.point 1 = coordinatePoint 1)
    (h2 : H.point 2 = coordinatePoint 3) :
    ∃ g : Model F, HasCoordinatePrefix (H.map g) := by
  let x := (H.point 3).val.rep
  have hx : x = ![0,x 1,0,0,0,x 5,0,x 7] :=
    annihilator_basis_five x (products_zero_of_coordinate_on 3
      (h2 ▸ H.point_on 2) (H.next_on 2))
  have h7 : x 7 ≠ 0 := by
    intro h7
    apply fourth_not_on_second H
    apply (pointOnLine_iff _ _).mpr
    have he : x = x 1 • offDiagonalVector 1 + x 5 • offDiagonalVector 3 := by
      calc
        x = ![0,x 1,0,0,0,x 5,0,x 7] := hx
        _ = x 1 • offDiagonalVector 1 + x 5 • offDiagonalVector 3 := by
          ext i
          fin_cases i <;> simp [offDiagonalVector, offDiagonalIndex, basisVector, h7]
    change x ∈ (H.line 1).val
    rw [he]
    exact (H.line 1).val.add_mem
      ((H.line 1).val.smul_mem (x 1) ((coordinatePoint_on_iff 1 _).mp (h1 ▸ H.point_on 1)))
      ((H.line 1).val.smul_mem (x 5) ((coordinatePoint_on_iff 3 _).mp (h2 ▸ H.next_on 1)))
  refine ⟨fourthReducer x, ?_, ?_, ?_, ?_⟩
  · rw [PointHexagon.map_point, h0]
    exact fixed_of_vector _ 0 (fourthReducer_fixes x).1
  · rw [PointHexagon.map_point, h1]
    exact fixed_of_vector _ 1 (fourthReducer_fixes x).2.1
  · rw [PointHexagon.map_point, h2]
    exact fixed_of_vector _ 3 (fourthReducer_fixes x).2.2
  · exact smul_point_eq_coordinate _ (H.point 3) 5 (x 7) (fourthReducer_apply x hx h7)

/-- An actual split-octonion automorphism sends the first four points to the
coordinate lines of basis vectors 0, 1, 5, and 7, respectively. -/
theorem normalize_prefix (H : PointHexagon F) :
    ∃ g : Model F, HasCoordinatePrefix (H.map g) := by
  obtain ⟨a,ha⟩ := exists_smul_firstPoint (H.point 0)
  have ha0 : (H.map a).point 0 = coordinatePoint 0 := ha
  obtain ⟨b,hb0,hb1⟩ := normalize_second (H.map a) ha0
  obtain ⟨c,hc0,hc1,hc2⟩ := normalize_third ((H.map a).map b) hb0 hb1
  obtain ⟨d,hd⟩ := normalize_fourth (((H.map a).map b).map c) hc0 hc1 hc2
  refine ⟨d * (c * (b * a)), ?_⟩
  simpa only [HasCoordinatePrefix, PointHexagon.map_point, SemigroupAction.mul_smul] using hd
end Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.Apartments
