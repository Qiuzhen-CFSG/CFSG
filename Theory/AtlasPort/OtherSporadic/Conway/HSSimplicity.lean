/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/HSSimplicity.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.HSPrimitivity
public import Theory.AtlasPort.OtherSporadic.GroupTheory.NormalOrderHundred

/-!
Simplicity of the concrete Higman–Sims triangle stabilizer.
Primitivity and the simple Mathieu22 point stabilizer reduce a proper normal subgroup to an impossible regular subgroup of order 100.

Source: Gerald Höhn, `Atlas/Conway/HSSimplicity.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices MulAction
attribute [local instance] Classical.propDecidable

theorem hs_normal_factor (N : Subgroup HSModel) [N.Normal]
    [IsPretransitive N HSGraphPoints] :
    ∀ g : HSModel, ∃ n : N, ∃ k : HSMathieuModel, g = n.val*hsMathieu22Embedding k := by
  intro g
  obtain ⟨n,hn⟩ := exists_smul_eq N hsBaseGraphPoint (g • hsBaseGraphPoint)
  have hk : n.val⁻¹*g ∈ HSGraphStabilizer := by
    change (n.val⁻¹*g) • hsBaseGraphPoint = hsBaseGraphPoint
    rw [mul_smul,← hn]
    exact inv_smul_smul n.val hsBaseGraphPoint
  obtain ⟨k,hk'⟩ := hsMathieuGraphEquiv.surjective ⟨n.val⁻¹*g,hk⟩
  have he : hsMathieu22Embedding k = n.val⁻¹*g := congrArg Subtype.val hk'
  exact ⟨n,k,by rw [he,mul_inv_cancel_left]⟩

theorem hs_regular_normal_impossible (N : Subgroup HSModel) [N.Normal]
    [IsPretransitive N HSGraphPoints]
    (hf : ∀ n : N, n • hsBaseGraphPoint = hsBaseGraphPoint → n = 1) : False := by
  have hi : Function.Injective (fun n : N => n • hsBaseGraphPoint) := by
    intro u v huv
    change u • hsBaseGraphPoint = v • hsBaseGraphPoint at huv
    have hh : (u⁻¹*v) • hsBaseGraphPoint = hsBaseGraphPoint := by
      rw [mul_smul,← huv,inv_smul_smul]
    exact inv_mul_eq_one.mp (hf _ hh)
  have hc : Nat.card N = 100 := by
    rw [← hs_graph_card]
    exact Nat.card_congr (Equiv.ofBijective _ ⟨hi,fun y => exists_smul_eq N hsBaseGraphPoint y⟩)
  let := hs_graph_primitive
  let := hs_graph_faithful
  exact Atlas.GroupTheory.primitive_no_normal_order_hundred hsBaseGraphPoint hs_graph_card N hc

theorem hs_simple : IsSimpleGroup HSModel := by
  let : Nontrivial HSModel := by
    obtain ⟨g,h,hne⟩ := hs_noncommuting_pair
    exact ⟨⟨g*h,h*g,hne⟩⟩
  let := hs_graph_primitive
  let := hs_graph_faithful
  let := hs_graph_stabilizer_simple
  constructor
  intro N hnormal
  let := hnormal
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  let := Atlas.GroupTheory.normal_pretransitive (X := HSGraphPoints) N hN
  rcases (inferInstance : (N.subgroupOf HSGraphStabilizer).Normal).eq_bot_or_eq_top with hb | ht
  · exact False.elim (hs_regular_normal_impossible N (by
      intro n hn
      have hm : (⟨n.val,hn⟩ : HSGraphStabilizer) ∈ N.subgroupOf HSGraphStabilizer := n.prop
      rw [hb,Subgroup.mem_bot] at hm
      exact Subtype.ext (congrArg (fun k : HSGraphStabilizer => (k : HSModel)) hm)))
  · apply top_unique
    intro g _
    obtain ⟨n,k,hg⟩ := hs_normal_factor N g
    have hk : hsMathieu22Embedding k ∈ N := by
      have hm : hsMathieuGraphEquiv k ∈ N.subgroupOf HSGraphStabilizer := by
        rw [ht]; trivial
      exact hm
    rw [hg]
    exact N.mul_mem n.prop hk

end Atlas.Conway
