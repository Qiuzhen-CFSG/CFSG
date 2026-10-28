/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/McLTriangleOrbits.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.McLTriangleTransport
public import Theory.AtlasPort.OtherSporadic.Conway.McLTriangleTransitivity

/-!
The four Mathieu22 orbits on McLaughlin triangles.
Shape invariance and within-shape transport identify orbit equivalence with
equality of shape type and recover the subdegrees from the parameter counts.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/McLTriangleOrbits.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definitions,
preserving source namespaces and the coordinate reductions used across modules.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

def mclTriangleType (y : McLTriangles) : Fin 4 :=
  if y.val.val co3MarkedCoordinate = -3 then 0
  else if y.val.val co3MarkedCoordinate = 1 then 1
  else if y.val.val co3MarkedCoordinate = -1 then 2 else 3

theorem mcl_triangle_shape_type (t : Fin 4) (y : McLTriangles)
    (h : McLTriangleShape t y.val) : mclTriangleType y = t := by
  have hc := congrArg Prod.fst (mcl_triangle_shape_coordinate_pair t y.val h)
  fin_cases t <;> norm_num at hc <;> simp [mclTriangleType,hc]

theorem mcl_triangle_type_shape (y : McLTriangles) :
    McLTriangleShape (mclTriangleType y) y.val := by
  obtain ⟨t,ht⟩ := mcl_triangle_shape_exhaustive y
  rw [mcl_triangle_shape_type t y ht]
  exact ht

theorem mcl_triangle_type_preserved (g : McLMathieuModel) (y : McLTriangles) :
    mclTriangleType (mclMathieu22Embedding g • y) = mclTriangleType y := by
  have ha : g.val.val.val co3MarkedCoordinate = co3MarkedCoordinate := g.val.prop
  have hi : g.val.val.val.symm co3MarkedCoordinate = co3MarkedCoordinate :=
    (g.val.val.val.symm_apply_eq).mpr ha.symm
  have he : (mclMathieu22Embedding g • y).val.val co3MarkedCoordinate =
      y.val.val co3MarkedCoordinate := by
    change y.val.val (g.val.val.val.symm co3MarkedCoordinate) = _
    rw [hi]
  simp only [mclTriangleType,he]

theorem mcl_triangle_mathieu_orbit_iff (x y : McLTriangles) :
    (∃ g : McLMathieuModel, mclMathieu22Embedding g • x = y) ↔
      mclTriangleType x = mclTriangleType y := by
  constructor
  · rintro ⟨g,rfl⟩
    exact (mcl_triangle_type_preserved g x).symm
  · intro ht
    obtain ⟨g,hg⟩ := mcl_triangle_shape_transitive (mclTriangleType x) x.val y.val
      (mcl_triangle_type_shape x) (by rw [ht]; exact mcl_triangle_type_shape y)
    exact ⟨g,Subtype.ext hg⟩

def mclTriangleShapeEquiv (t : Fin 4) :
    McLTriangleParameters t ≃ {y : leech // McLTriangleShape t y} :=
  Equiv.ofBijective (fun p => ⟨mclTriangleParameterVector t p,mcl_triangle_parameter_shape t p⟩)
    ⟨fun p q h => mclTriangleParameterVector_injective t (congrArg Subtype.val h),by
      intro y
      obtain ⟨p,hp⟩ := mcl_triangle_parameter_represents t y.val y.prop
      exact ⟨p,Subtype.ext hp⟩⟩

def mclTriangleTypeShapeEquiv (t : Fin 4) :
    {y : McLTriangles // mclTriangleType y = t} ≃ {y : leech // McLTriangleShape t y} where
  toFun y := ⟨y.val.val,Eq.mp (congrArg (fun k => McLTriangleShape k y.val.val) y.prop) (mcl_triangle_type_shape y.val)⟩
  invFun y := ⟨⟨y.val,mcl_triangle_shape_sound t y.val y.prop⟩,
    mcl_triangle_shape_type t _ y.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem mcl_triangle_type_card (t : Fin 4) :
    Nat.card {y : McLTriangles // mclTriangleType y = t} = mclTriangleSize t := by
  rw [Nat.card_congr (mclTriangleTypeShapeEquiv t),
    ← Nat.card_congr (mclTriangleShapeEquiv t),mcl_triangle_parameters_card]

theorem mcl_base_triangle_type : mclTriangleType mclBaseTriangle = 0 :=
  mcl_triangle_shape_type 0 _ rfl

end Atlas.Conway
