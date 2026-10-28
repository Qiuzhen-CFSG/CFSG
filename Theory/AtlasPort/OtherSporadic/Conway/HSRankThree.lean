/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/HSRankThree.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.HSOrder

/-!
Rank three of the Higman–Sims graph action.
The invariant local-family map identifies the stabilizer orbit quotient with Fin 3.

Source: Gerald Höhn, `Atlas/Conway/HSRankThree.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices MulAction
attribute [local instance] Classical.propDecidable

theorem hs_local_family_invariant (g : HSGraphStabilizer) (y : HSGraphPoints) :
    hsLocalFamily (g • y) = hsLocalFamily y := by
  obtain ⟨q,rfl⟩ := hsMathieuGraphEmbedding_bijective.surjective g
  obtain ⟨v,rfl⟩ := hsWittGraphMap_surjective y
  rcases v with v | (v | v)
  · change hsLocalFamily ((hsMathieuGraphEmbedding q).val • hsBaseGraphPoint) = hsLocalFamily hsBaseGraphPoint
    rw [(hsMathieuGraphEmbedding q).prop]
  · change hsLocalFamily (hsMathieu22Embedding q • hsPointVector v) = hsLocalFamily (hsPointVector v)
    rw [← hs_point_label_equivariant]
    simp only [hsPointVector,hs_local_family_witt,hsWittFamily]
  · change hsLocalFamily (hsMathieu22Embedding q • hsHexadVector v) = hsLocalFamily (hsHexadVector v)
    rw [← hs_hexad_equivariant]
    simp only [hsHexadVector,hs_local_family_witt,hsWittFamily]

theorem hs_local_family_surjective : Function.Surjective hsLocalFamily := by
  intro i
  have hp : 0 < Nat.card {y : HSGraphPoints // hsLocalFamily y = i} := by
    rw [hs_local_fiber_card]
    fin_cases i <;> decide
  obtain ⟨y⟩ := (Nat.card_pos_iff.mp hp).1
  exact ⟨y.val,y.prop⟩

def hsLocalOrbitEquiv : orbitRel.Quotient HSGraphStabilizer HSGraphPoints ≃ Fin 3 :=
  (show orbitRel.Quotient HSGraphStabilizer HSGraphPoints ≃ Quotient (Setoid.ker hsLocalFamily) from
    Quotient.congrRight (fun x y => by
    change orbitRel HSGraphStabilizer HSGraphPoints x y ↔ hsLocalFamily x = hsLocalFamily y
    rw [orbitRel_apply]
    constructor
    · rintro ⟨g,rfl⟩
      exact hs_local_family_invariant g y
    · intro he
      obtain ⟨g,hg⟩ := hs_local_family_transitive y x he.symm
      exact ⟨g,hg⟩)).trans
    (Setoid.quotientKerEquivOfSurjective hsLocalFamily hs_local_family_surjective)

theorem hs_graph_rank_three : Nat.card (orbitRel.Quotient HSGraphStabilizer HSGraphPoints) = 3 := by
  rw [Nat.card_congr hsLocalOrbitEquiv,Nat.card_fin]

end Atlas.Conway
