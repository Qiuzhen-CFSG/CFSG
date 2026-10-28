/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/HSPointAction.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.HSMathieu22

/-!
The action on the 22 coordinate vertices of the Higman–Sims graph.
The explicit Mathieu embedding identifies its point-label action and proves faithfulness on the graph.

Source: Gerald Höhn, `Atlas/Conway/HSPointAction.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

instance hsPointLabelAction : MulAction HSMathieuModel HSPointLabels :=
  mathieu22MulAction co3MarkedCoordinate co3BasePoint

def hsPointVector (c : HSPointLabels) : HSGraphPoints := hsWittGraphMap (Sum.inr (Sum.inl c))

theorem hsPointVector_injective : Function.Injective hsPointVector := by
  intro c d he
  exact Sum.inl.inj (Sum.inr.inj (hsWittGraphMap_injective he))

theorem hs_point_label_equivariant (g : HSMathieuModel) (c : HSPointLabels) :
    hsPointVector (g • c) = hsMathieu22Embedding g • hsPointVector c := by
  apply Subtype.ext
  change minimumPairPlus co3MarkedCoordinate (g • c).val.val =
    (permutationEmbedding g.val.val).val (minimumPairPlus co3MarkedCoordinate c.val.val)
  rw [(permutation_minimumPair _ _ _).1]
  have hi : g.val.val.val co3MarkedCoordinate = co3MarkedCoordinate := g.val.prop
  rw [hi]
  rfl

theorem hs_point_labels_transitive : MulAction.IsPretransitive HSMathieuModel HSPointLabels := by
  let : MulAction.IsMultiplyPretransitive HSMathieuModel HSPointLabels 3 :=
    mathieu22_three_transitive co3MarkedCoordinate co3BasePoint
  have h2 : MulAction.IsMultiplyPretransitive HSMathieuModel HSPointLabels 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := 3) (by decide) (by
      change 3 ≤ Nat.card (Mathieu22Points co3MarkedCoordinate co3BasePoint)
      rw [mathieu22_degree]; decide)
  exact @MulAction.isPretransitive_of_is_two_pretransitive HSMathieuModel HSPointLabels _ _ h2

theorem hs_graph_faithful : FaithfulSMul HSModel HSGraphPoints := by
  apply faithfulSMul_iff.mpr
  intro g hg
  let k : HSGraphStabilizer := ⟨g,hg hsBaseGraphPoint⟩
  let q := hsMathieuGraphEquiv.symm k
  have he : hsMathieu22Embedding q = g := congrArg Subtype.val (hsMathieuGraphEquiv.apply_symm_apply k)
  have hq : q = 1 := by
    let := mathieu22_faithful co3MarkedCoordinate co3BasePoint
    apply (faithfulSMul_iff (G := HSMathieuModel) (α := HSPointLabels)).mp
      (mathieu22_faithful co3MarkedCoordinate co3BasePoint) q
    intro c
    apply hsPointVector_injective
    rw [hs_point_label_equivariant,he,hg]
  rw [hq,map_one] at he
  exact he.symm

instance hsMathieuGraphAction : MulAction HSMathieuModel HSGraphPoints :=
  MulAction.compHom _ hsMathieu22Embedding

theorem hs_point_family_orbit (c : HSPointLabels) :
    MulAction.orbit HSMathieuModel (hsPointVector c) = Set.range hsPointVector := by
  let := hs_point_labels_transitive
  ext y
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨g • c,hs_point_label_equivariant g c⟩
  · rintro ⟨d,rfl⟩
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq HSMathieuModel c d
    refine ⟨g,?_⟩
    change hsMathieu22Embedding g • hsPointVector c = hsPointVector d
    rw [← hs_point_label_equivariant,hg]

end Atlas.Conway
