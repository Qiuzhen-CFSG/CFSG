/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/HSHexadAction.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.HSPointAction
public import Theory.AtlasPort.OtherSporadic.Conway.HSHexadComparison
public import Theory.AtlasPort.OtherSporadic.Combinatorics.SteinerBlockTransitivity

/-!
The Mathieu22 action on the 77 hexad vertices.
Equivariance of the explicit lattice vectors transfers transitivity from the hexad design.

Source: Gerald Höhn, `Atlas/Conway/HSHexadAction.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices Atlas.Combinatorics
attribute [local instance] Classical.propDecidable
local instance : Fintype (Mathieu23Points co3MarkedCoordinate) := Fintype.ofFinite _
local instance : Fintype HSPointLabels := Fintype.ofFinite _

def hsHexadVector (B : HSHexadLabels) : HSGraphPoints := hsWittGraphMap (Sum.inr (Sum.inr B))

theorem hsHexadVector_injective : Function.Injective hsHexadVector := by
  intro B C he
  exact Sum.inr.inj (Sum.inr.inj (hsWittGraphMap_injective he))

def hsHexadMap (g : HSMathieuModel) (B : HSHexadLabels) : HSHexadLabels :=
  ⟨⟨mathieu23PermuteBlock co3MarkedCoordinate g.val B.val.val,
    mathieu23Blocks_preserved _ _ _ B.val.prop⟩,by
    change co3BasePoint ∈ B.val.val.image (fun b => g.val • b)
    exact Finset.mem_image.mpr ⟨co3BasePoint,B.prop,g.prop⟩⟩

theorem hs_hexad_equivariant (g : HSMathieuModel) (B : HSHexadLabels) :
    hsHexadVector (hsHexadMap g B) = hsMathieu22Embedding g • hsHexadVector B := by
  apply Subtype.ext
  change normSixVector co3MarkedCoordinate-co3HeptadEndpoint _ (hsHexadMap g B).val =
    (permutationEmbedding g.val.val).val (normSixVector co3MarkedCoordinate-co3HeptadEndpoint _ B.val)
  have hx : (permutationEmbedding g.val.val).val (normSixVector co3MarkedCoordinate) =
      normSixVector co3MarkedCoordinate := (Atlas.Sporadic.Conway3.mathieu23Embedding g.val).prop
  rw [map_sub,hx]
  exact congrArg (fun v : leech => normSixVector co3MarkedCoordinate-v)
    (co3EvenEndpoint_equivariant _ g.val (Sum.inr B.val))

theorem hs_hexad_restore (B : HSHexadLabels) : B.val.val =
    insert co3BasePoint (mathieu22BlockLift co3MarkedCoordinate co3BasePoint (hsHexadLabelEquiv B).val) := by
  let e := derivedBlocksThroughEquiv (mathieu23Blocks co3MarkedCoordinate) co3BasePoint
  exact (congrArg Subtype.val (e.apply_symm_apply ⟨B.val.val,B.val.prop,B.prop⟩)).symm

theorem hs_hexad_labels_transitive (B C : HSHexadLabels) :
    ∃ g : HSMathieuModel, hsHexadMap g B = C := by
  let : MulAction.IsMultiplyPretransitive HSMathieuModel HSPointLabels 3 :=
    mathieu22_three_transitive _ _
  have hperm (g : HSMathieuModel) (D : Finset HSPointLabels) :
      D.image (fun v => g • v) = mathieu22PermuteBlock co3MarkedCoordinate co3BasePoint g D := by
    ext c
    simp only [mathieu22PermuteBlock,Finset.mem_image]
    rfl
  obtain ⟨g,hg⟩ := steiner_block_transitive (G := HSMathieuModel) (V := HSPointLabels) (t := 3) (k := 6)
    (mathieu22Blocks co3MarkedCoordinate co3BasePoint) (by decide)
    (mathieu22Blocks_size _ _) (mathieu22_steiner _ _)
    (fun g B hB => by
      rw [hperm g B]
      exact mathieu22Blocks_preserved co3MarkedCoordinate co3BasePoint g B hB)
    (hsHexadLabelEquiv B).val (hsHexadLabelEquiv C).val
    (hsHexadLabelEquiv B).prop (hsHexadLabelEquiv C).prop
  refine ⟨g,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change mathieu23PermuteBlock co3MarkedCoordinate g.val B.val.val = C.val.val
  rw [hs_hexad_restore B,hs_hexad_restore C]
  rw [hperm g (hsHexadLabelEquiv B).val] at hg
  have he := congrArg (mathieu22BlockLift co3MarkedCoordinate co3BasePoint) hg
  rw [mathieu22BlockLift_permute] at he
  unfold mathieu23PermuteBlock
  have hp : puncturedRestrictionPerm co3MarkedCoordinate g.val co3BasePoint = co3BasePoint := g.prop
  rw [Finset.image_insert,hp]
  exact congrArg (insert co3BasePoint) he

theorem hs_hexad_family_orbit (B : HSHexadLabels) :
    MulAction.orbit HSMathieuModel (hsHexadVector B) = Set.range hsHexadVector := by
  ext y
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨hsHexadMap g B,hs_hexad_equivariant g B⟩
  · rintro ⟨C,rfl⟩
    obtain ⟨g,hg⟩ := hs_hexad_labels_transitive B C
    refine ⟨g,?_⟩
    change hsMathieu22Embedding g • hsHexadVector B = hsHexadVector C
    rw [← hs_hexad_equivariant,hg]

end Atlas.Conway
