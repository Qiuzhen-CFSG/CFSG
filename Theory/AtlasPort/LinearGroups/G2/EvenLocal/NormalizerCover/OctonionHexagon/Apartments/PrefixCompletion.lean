module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The coordinate reduction uses the root formulas of
Atlas/LinearGroups/G2/RootLinearMaps.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: complete the last two points of an intrinsic octonion hexagon after
normalizing its first four points, using the actual root E automorphism.
-/

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Apartments.Configurations
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Apartments.CoordinateCalculations

/-!
# Completing an octonion hexagon with a coordinate prefix

Assume the first four points are the basis lines 0, 1, 5, 7. Incidence with
the two endpoints places the remaining representatives in their annihilators.
Their common zero-product line and point distinctness then give representatives
`x = ![0,0,0,0,0,a,b,0]` and `y = ![0,e,f,0,0,0,0,0]`, where `b` and `f`
are nonzero and `a*f + b*e = 0`. The root element `rootE (-a/b)` sends these
to the basis lines 6 and 2 while fixing all four prefix vectors.

This calculation works over every field. It assumes the coordinate prefix;
constructing that prefix is a separate geometric normalization step.

Source context: the split G₂ case of Aschbacher--Smith, Theorem 0.1.2(1),
printed pp.3--4, repeated as Theorem 0.1.1 on pp.481--482. The concrete
coordinates and root formulas use the licensed ATLAS port cited above.
-/

public section

open Atlas.G2 Atlas.G2.Explicit Atlas.SplitOctonion
open scoped LinearAlgebra.Projectivization

namespace Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.Apartments
variable {F : Type*} [Field F]

private theorem point_eq_coordinate_of_rep (p : SingularPoints F) (i : Fin 6) (a : F)
    (h : p.val.rep = a • offDiagonalVector i) : p = coordinatePoint i := by
  rw [← singularPointMk_rep F p, coordinatePoint]
  apply Subtype.ext
  exact (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr ⟨a, h.symm⟩

private theorem smul_point_eq_coordinate (g : Model F) (p : SingularPoints F)
    (i : Fin 6) (a : F) (h : g.val p.val.rep = a • offDiagonalVector i) :
    g • p = coordinatePoint i := by
  rw [← singularPointMk_rep F p, singularPointMk_smul, coordinatePoint]
  apply Subtype.ext
  exact (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr ⟨a, h.symm⟩

private theorem prefix_last_reps (H : PointHexagon F) (hprefix : HasCoordinatePrefix H) :
    let x := (H.point 4).val.rep
    let y := (H.point 5).val.rep
    x = ![0,0,0,0,0,x 5,x 6,0] ∧ y = ![0,y 1,y 2,0,0,0,0,0] ∧
      x 6 ≠ 0 ∧ y 2 ≠ 0 ∧ x 5 * y 2 + x 6 * y 1 = 0 := by
  rcases hprefix with ⟨h0, h1, h2, h3⟩
  let x := (H.point 4).val.rep
  let y := (H.point 5).val.rep
  have hx : x = ![0,0,0,0,0,x 5,x 6,x 7] := by
    apply annihilator_basis_seven
    have hp := products_zero_of_coordinate_on 5 (h3 ▸ H.point_on 3) (H.next_on 3)
    simpa [x, offDiagonalVector, offDiagonalIndex] using hp
  have hy : y = ![y 0,y 1,y 2,0,0,0,0,0] := by
    apply annihilator_basis_zero
    have hp := products_zero_of_coordinate_on 0 (h0 ▸ H.next_on 5) (H.point_on 5)
    simpa only [offDiagonalVector, offDiagonalIndex, Matrix.cons_val] using hp
  have hp : mul x y = 0 := (products_zero_of_pointOnLine (H.point_on 4) (H.next_on 4)).1
  have had : x 5 * y 0 = 0 := by
    have h := congrFun hp 1
    rw [hx, hy] at h
    simpa [mul] using h
  have hbd : x 6 * y 0 = 0 := by
    have h := congrFun hp 2
    rw [hx, hy] at h
    simpa [mul] using h
  have hce : x 7 * y 1 = 0 := by
    have h := congrFun hp 5
    rw [hx, hy] at h
    simpa [mul] using h
  have hcf : x 7 * y 2 = 0 := by
    have h := congrFun hp 6
    rw [hx, hy] at h
    simpa [mul] using h
  have hrel : x 5 * y 2 + x 6 * y 1 = 0 := by
    have h := congrFun hp 3
    rw [hx, hy] at h
    have h' : -(x 5 * y 2) - x 6 * y 1 = 0 := by simpa [mul] using h
    apply neg_eq_zero.mp
    simpa only [neg_add, sub_eq_add_neg] using h'
  -- Otherwise the fifth point would equal the fourth prefix point.
  have hd : y 0 = 0 := by
    by_contra hd
    have ha := (mul_eq_zero.mp had).resolve_right hd
    have hb := (mul_eq_zero.mp hbd).resolve_right hd
    have he : H.point 4 = H.point 3 := by
      rw [h3]
      apply point_eq_coordinate_of_rep _ 5 (x 7)
      change x = _
      rw [hx]
      ext i
      fin_cases i <;> simp [ha, hb, offDiagonalVector, offDiagonalIndex, basisVector]
    have hi := H.point_injective he
    contradiction
  -- Otherwise the sixth point would equal the first prefix point.
  have hc : x 7 = 0 := by
    by_contra hc
    have he := (mul_eq_zero.mp hce).resolve_left hc
    have hf := (mul_eq_zero.mp hcf).resolve_left hc
    have heq : H.point 5 = H.point 0 := by
      rw [h0]
      apply point_eq_coordinate_of_rep _ 0 (y 0)
      change y = _
      rw [hy]
      ext i
      fin_cases i <;> simp [he, hf, offDiagonalVector, offDiagonalIndex, basisVector]
    have hi := H.point_injective heq
    contradiction
  have hb : x 6 ≠ 0 := by
    intro hb
    have he : H.point 4 = H.point 2 := by
      rw [h2]
      apply point_eq_coordinate_of_rep _ 3 (x 5)
      change x = _
      rw [hx]
      ext i
      fin_cases i <;> simp [hb, hc, offDiagonalVector, offDiagonalIndex, basisVector]
    have hi := H.point_injective he
    contradiction
  have hf : y 2 ≠ 0 := by
    intro hf
    have he : H.point 5 = H.point 1 := by
      rw [h1]
      apply point_eq_coordinate_of_rep _ 1 (y 1)
      change y = _
      rw [hy]
      ext i
      fin_cases i <;> simp [hd, hf, offDiagonalVector, offDiagonalIndex, basisVector]
    have hi := H.point_injective he
    contradiction
  exact ⟨by simpa only [hc] using hx, by simpa only [hd] using hy, hb, hf, hrel⟩

private theorem rootE_last_reps (x y : Carrier F)
    (hx : x = ![0,0,0,0,0,x 5,x 6,0])
    (hy : y = ![0,y 1,y 2,0,0,0,0,0])
    (hb : x 6 ≠ 0) (hrel : x 5 * y 2 + x 6 * y 1 = 0) :
    (rootE (-x 5 / x 6)).val x = x 6 • basisVector 6 ∧
      (rootE (-x 5 / x 6)).val y = y 2 • basisVector 2 := by
  have hcancel : y 1 - (-x 5 / x 6) * y 2 = 0 := by
    apply (mul_right_cancel₀ hb)
    calc
      (y 1 - (-x 5 / x 6) * y 2) * x 6 = x 5 * y 2 + x 6 * y 1 := by
        field_simp
        ring
      _ = 0 * x 6 := by rw [hrel, zero_mul]
  constructor
  · rw [hx]
    ext i
    fin_cases i <;> simp [rootE, rootEEquiv, rootELinear, rootEApply, basisVector, hb]
  · rw [hy]
    ext i
    fin_cases i <;> simp [rootE, rootEEquiv, rootELinear, rootEApply, basisVector, hcancel]

/-- Complete a point hexagon whose first four points are the coordinate prefix,
over an arbitrary field, by an actual split-octonion automorphism. -/
theorem complete_coordinate_prefix (H : PointHexagon F) (hprefix : HasCoordinatePrefix H) :
    ∃ g : Model F, ∀ i : Fin 6, ∃ j : Fin 6, g • H.point j = coordinatePoint i := by
  obtain ⟨hx, hy, hb, _, hrel⟩ := prefix_last_reps H hprefix
  let x := (H.point 4).val.rep
  let y := (H.point 5).val.rep
  let g : Model F := rootE (-x 5 / x 6)
  have hlast := rootE_last_reps x y hx hy hb hrel
  have hfix := rootE_fixes_prefix (-x 5 / x 6)
  have hcoord (i : Fin 6) (hi : g.val (offDiagonalVector i) = offDiagonalVector i) :
      g • coordinatePoint i = coordinatePoint i :=
    (coordinatePoint_fixed_iff g i).mpr ⟨1, by simpa using hi⟩
  rcases hprefix with ⟨h0, h1, h2, h3⟩
  refine ⟨g, ?_⟩
  intro i
  fin_cases i
  · exact ⟨0, h0 ▸ hcoord 0 hfix.1⟩
  · exact ⟨1, h1 ▸ hcoord 1 hfix.2.1⟩
  · exact ⟨5, smul_point_eq_coordinate g (H.point 5) 2 (y 2) hlast.2⟩
  · exact ⟨2, h2 ▸ hcoord 3 hfix.2.2.1⟩
  · exact ⟨4, smul_point_eq_coordinate g (H.point 4) 4 (x 6) hlast.1⟩
  · exact ⟨3, h3 ▸ hcoord 5 hfix.2.2.2⟩

end Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.Apartments
