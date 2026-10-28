/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/McLMathieu22.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.McLGraph
public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu22Simplicity

/-!
The actual Mathieu22 subgroup inside the McLaughlin triangle stabilizer.
The coordinate action gives an injective embedding, a noncommuting pair,
and a primitive equivariant orbit on the 22 point-family vertices.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/McLMathieu22.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definitions,
preserving source namespaces and the coordinate reductions used across modules.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

abbrev McLMathieuModel := Mathieu22PointModel co3MarkedCoordinate co3BasePoint

def mclMathieu22Embedding : McLMathieuModel →* McLModel where
  toFun g := ⟨Atlas.Sporadic.Conway3.mathieu23Embedding g.val,by
    change (permutationEmbedding g.val.val).val mclEndpoint = mclEndpoint
    unfold mclEndpoint
    rw [(permutation_minimumPair _ _ _).1]
    have hi : g.val.val.val co3MarkedCoordinate = co3MarkedCoordinate := g.val.prop
    have hp : g.val.val.val co3BasePoint.val = co3BasePoint.val := congrArg Subtype.val g.prop
    rw [hi,hp]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem mclMathieu22Embedding_injective : Function.Injective mclMathieu22Embedding := by
  intro g h he
  apply Subtype.ext
  apply Atlas.Sporadic.Conway3.mathieu23Embedding_injective
  exact congrArg Subtype.val he

theorem mcl_noncommuting_pair : ∃ g h : McLModel, g*h ≠ h*g := by
  obtain ⟨g,h,hne⟩ := mathieu22_noncommuting_pair co3MarkedCoordinate co3BasePoint
  refine ⟨mclMathieu22Embedding g,mclMathieu22Embedding h,?_⟩
  intro he
  apply hne
  apply mclMathieu22Embedding_injective
  simpa only [map_mul] using he

instance mclPointLabelAction : MulAction McLMathieuModel McLPointLabels :=
  mathieu22MulAction co3MarkedCoordinate co3BasePoint

theorem mcl_point_labels_primitive : MulAction.IsPreprimitive McLMathieuModel McLPointLabels := by
  let h3 : MulAction.IsMultiplyPretransitive McLMathieuModel McLPointLabels 3 :=
    mathieu22_three_transitive co3MarkedCoordinate co3BasePoint
  have h2 : MulAction.IsMultiplyPretransitive McLMathieuModel McLPointLabels 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := 3) (by decide) (by
      change 3 ≤ Nat.card (Mathieu22Points co3MarkedCoordinate co3BasePoint)
      rw [mathieu22_degree]; decide)
  exact MulAction.isPreprimitive_of_is_two_pretransitive h2

theorem mcl_point_label_equivariant (g : McLMathieuModel) (c : McLPointLabels) :
    mclWittVector (Sum.inl (g • c)) = mclMathieu22Embedding g • mclWittVector (Sum.inl c) := by
  apply Subtype.ext
  change minimumPairPlus co3MarkedCoordinate (g • c).val.val =
    (permutationEmbedding g.val.val).val (minimumPairPlus co3MarkedCoordinate c.val.val)
  rw [(permutation_minimumPair _ _ _).1]
  have hi : g.val.val.val co3MarkedCoordinate = co3MarkedCoordinate := g.val.prop
  rw [hi]
  rfl

theorem mcl_point_labels_transitive : MulAction.IsPretransitive McLMathieuModel McLPointLabels := by
  let := mcl_point_labels_primitive
  infer_instance

theorem mcl_mathieu_simple : IsSimpleGroup McLMathieuModel := mathieu22_simple _ _

theorem mcl_mathieu_card : Nat.card McLMathieuModel = 443520 := mathieu22_order _ _


instance mclMathieuGraphAction : MulAction McLMathieuModel McLGraphPoints :=
  MulAction.compHom _ mclMathieu22Embedding

theorem mcl_point_family_orbit (c : McLPointLabels) :
    MulAction.orbit McLMathieuModel (mclWittVector (Sum.inl c)) =
      Set.range (fun d : McLPointLabels => mclWittVector (Sum.inl d)) := by
  let := mcl_point_labels_transitive
  ext y
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨g • c,mcl_point_label_equivariant g c⟩
  · rintro ⟨d,rfl⟩
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq McLMathieuModel c d
    refine ⟨g,?_⟩
    rw [← hg]
    exact (mcl_point_label_equivariant g c).symm

def mclPointFamilyEquiv : McLPointLabels ≃
    Set.range (fun d : McLPointLabels => mclWittVector (Sum.inl d)) :=
  Equiv.ofInjective _ (fun _ _ h => Sum.inl.inj (mclWittVector_injective h))

theorem mcl_point_family_card :
    Nat.card (Set.range (fun d : McLPointLabels => mclWittVector (Sum.inl d))) = 22 := by
  rw [← Nat.card_congr mclPointFamilyEquiv]
  exact mcl_witt_label_cards.1

end Atlas.Conway
