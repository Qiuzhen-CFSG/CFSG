/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/McLTriangleStabilizer.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.McLMathieu22
public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleShapes

/-!
A second Leech triangle slice and its actual Mathieu22 stabilizer.
The coordinate action fixes a reference triangle, and the Conway3 triangle
stabilizer description proves that every stabilizer element comes from Mathieu22.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/McLTriangleStabilizer.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definitions,
preserving source namespaces and the coordinate reductions used across modules.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

def mclReferenceVector : leech := oddMinimumVector co3MarkedCoordinate 0

abbrev McLTriangles := LeechTriangleSlice (normSixVector co3MarkedCoordinate) mclEndpoint 32 8 (-8)

instance mclTrianglesAction : MulAction McLModel McLTriangles :=
  leechTriangleSliceAction _ _ _ _ _

def mclBaseTriangle : McLTriangles := ⟨mclReferenceVector,oddMinimumVector_norm _,
  ((co3_triangle_iff _ _).mp (co3_base_triangle_norms _)).2,by
  change integerDot (minimumPairPlus _ _).val (oddMinimumVector _ 0).val = -8
  rw [minimumPairPlus_dot,oddMinimumVector_zero_apply,oddMinimumVector_zero_apply]
  decide⟩

abbrev McLTriangleStabilizer := MulAction.stabilizer McLModel mclBaseTriangle

def mclMathieuTriangleEmbedding : McLMathieuModel →* McLTriangleStabilizer where
  toFun g := ⟨mclMathieu22Embedding g,Subtype.ext (mathieu23_fixes_triangle _ g.val)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem mclMathieuTriangleEmbedding_bijective : Function.Bijective mclMathieuTriangleEmbedding := by
  constructor
  · intro g h he
    apply mclMathieu22Embedding_injective
    exact congrArg Subtype.val he
  · intro g
    have hr : g.val.val.val.val mclReferenceVector = mclReferenceVector := congrArg Subtype.val g.prop
    obtain ⟨p,hp⟩ := co3_triangle_fixer_eq_permutation co3MarkedCoordinate
      g.val.val.val g.val.val.prop hr
    have ha : (permutationEmbedding p.val).val mclEndpoint = mclEndpoint := by
      rw [hp]; exact g.val.prop
    have hi : p.val.val co3MarkedCoordinate = co3MarkedCoordinate := p.prop
    have hpa : p • co3BasePoint = co3BasePoint := by
      apply Subtype.ext
      have he := congrArg (fun y : leech => y.val co3BasePoint.val) ha
      unfold mclEndpoint at he
      rw [(permutation_minimumPair _ _ _).1,hi] at he
      have hbi : co3BasePoint.val ≠ co3MarkedCoordinate := co3BasePoint.prop
      simp only [minimumPairPlus,coordinateVector,Pi.add_apply,Pi.single_apply,if_neg hbi] at he
      split_ifs at he with hh
      · exact hh.symm
      · norm_num at he
    let q : McLMathieuModel := ⟨p,hpa⟩
    refine ⟨q,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hp

def mclMathieuTriangleEquiv : McLMathieuModel ≃* McLTriangleStabilizer :=
  MulEquiv.ofBijective mclMathieuTriangleEmbedding mclMathieuTriangleEmbedding_bijective

theorem mcl_triangle_stabilizer_card : Nat.card McLTriangleStabilizer = 443520 := by
  rw [← Nat.card_congr mclMathieuTriangleEquiv.toEquiv,mcl_mathieu_card]

theorem mcl_triangle_stabilizer_simple : IsSimpleGroup McLTriangleStabilizer := by
  let := mcl_mathieu_simple
  exact mclMathieuTriangleEquiv.symm.isSimpleGroup

end Atlas.Conway
