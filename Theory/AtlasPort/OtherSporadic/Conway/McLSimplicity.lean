/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/McLSimplicity.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Sporadic.McLaughlinTriangles
public import Theory.AtlasPort.OtherSporadic.GroupTheory.TwoActionObstruction
public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimitiveNormal

/-!
Simplicity of the actual McLaughlin triangle stabilizer.
A nontrivial normal subgroup is transitive on triangles. Simplicity of the
Mathieu22 stabilizer gives either the whole group or a regular normal subgroup;
the second action on 275 vertices excludes the regular case.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/McLSimplicity.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definitions,
preserving source namespaces and the coordinate reductions used across modules.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices MulAction
attribute [local instance] Classical.propDecidable

theorem mcl_normal_factor (N : Subgroup McLModel) [N.Normal]
    [IsPretransitive N McLTriangles] :
    ∀ g : McLModel, ∃ n : N, ∃ k : McLMathieuModel, g = n.val*mclMathieu22Embedding k := by
  intro g
  obtain ⟨n,hn⟩ := exists_smul_eq N mclBaseTriangle (g • mclBaseTriangle)
  have hk : n.val⁻¹*g ∈ McLTriangleStabilizer := by
    change (n.val⁻¹*g) • mclBaseTriangle = mclBaseTriangle
    rw [mul_smul,← hn]
    exact inv_smul_smul n.val mclBaseTriangle
  obtain ⟨k,hk'⟩ := mclMathieuTriangleEquiv.surjective ⟨n.val⁻¹*g,hk⟩
  have he : mclMathieu22Embedding k = n.val⁻¹*g := congrArg Subtype.val hk'
  exact ⟨n,k,by rw [he,mul_inv_cancel_left]⟩

theorem mcl_regular_normal_impossible (N : Subgroup McLModel) [N.Normal]
    [IsPretransitive N McLTriangles]
    (hf : ∀ n : N, n • mclBaseTriangle = mclBaseTriangle → n = 1) : False := by
  have hi : Function.Injective (fun n : N => n • mclBaseTriangle) := by
    intro u v huv
    change u • mclBaseTriangle = v • mclBaseTriangle at huv
    have huv' : (u⁻¹*v) • mclBaseTriangle = mclBaseTriangle := by
      rw [mul_smul,← huv,inv_smul_smul]
    exact inv_mul_eq_one.mp (hf _ huv')
  have hc : Nat.card N = 2025 := by
    rw [← mcl_triangles_card]
    exact Nat.card_congr (Equiv.ofBijective _
      ⟨hi,fun y => exists_smul_eq N mclBaseTriangle y⟩)
  let := mcl_point_labels_primitive
  let := mcl_graph_transitive
  let j : McLPointLabels →ₑ[mclMathieu22Embedding] McLGraphPoints := {
    toFun c := mclWittVector (Sum.inl c)
    map_smul' := mcl_point_label_equivariant }
  apply Atlas.GroupTheory.normal_factor_two_action_obstruction mclMathieu22Embedding j
    mclBaseGraphLabel N (mcl_normal_factor N)
  · rw [mcl_witt_label_cards.1,mcl_graph_card]
    decide
  · rw [mcl_graph_card,hc]
    decide

theorem mcl_simple : IsSimpleGroup McLModel := by
  let : Nontrivial McLModel := by
    obtain ⟨g,h,hne⟩ := mcl_noncommuting_pair
    exact ⟨⟨g*h,h*g,hne⟩⟩
  let := mcl_triangles_primitive
  let := mcl_triangles_faithful
  let := mcl_triangle_stabilizer_simple
  constructor
  intro N hnormal
  let := hnormal
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  let := Atlas.GroupTheory.normal_pretransitive (X := McLTriangles) N hN
  rcases (inferInstance : (N.subgroupOf McLTriangleStabilizer).Normal).eq_bot_or_eq_top with hb | ht
  · exact False.elim (mcl_regular_normal_impossible N (by
      intro n hn
      have hm : (⟨n.val,hn⟩ : McLTriangleStabilizer) ∈ N.subgroupOf McLTriangleStabilizer := n.prop
      rw [hb,Subgroup.mem_bot] at hm
      exact Subtype.ext (congrArg (fun k : McLTriangleStabilizer => (k : McLModel)) hm)))
  · apply top_unique
    intro g _
    obtain ⟨n,k,hg⟩ := mcl_normal_factor N g
    have hk : mclMathieu22Embedding k ∈ N := by
      have hm : mclMathieuTriangleEquiv k ∈ N.subgroupOf McLTriangleStabilizer := by
        rw [ht]; trivial
      exact hm
    rw [hg]
    exact N.mul_mem n.prop hk

end Atlas.Conway
