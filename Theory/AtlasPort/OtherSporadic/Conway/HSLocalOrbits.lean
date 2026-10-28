/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/HSLocalOrbits.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.HSHexadAction

/-!
The three local families in the Higman–Sims graph.
The Mathieu22 stabilizer is transitive on each family, whose sizes are 1, 22, and 77.

Source: Gerald Höhn, `Atlas/Conway/HSLocalOrbits.lean`, ATLAS revision
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

/-- The three actual local families: base, coordinates, hexads. -/
def hsWittFamily : HSWittVertices → Fin 3
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

def hsLocalFamily (y : HSGraphPoints) : Fin 3 := hsWittFamily (hsWittVertexEquiv.symm y)

theorem hs_local_family_witt (v : HSWittVertices) : hsLocalFamily (hsWittGraphMap v) = hsWittFamily v := by
  change hsWittFamily (hsWittVertexEquiv.symm (hsWittVertexEquiv v)) = _
  rw [hsWittVertexEquiv.symm_apply_apply]

theorem hs_local_zero : {y : HSGraphPoints | hsLocalFamily y = 0} = {hsBaseGraphPoint} := by
  ext y
  obtain ⟨v,rfl⟩ := hsWittGraphMap_surjective y
  rw [Set.mem_ofPred_eq,hs_local_family_witt,Set.mem_singleton_iff]
  change hsWittFamily v = 0 ↔ hsWittGraphMap v = hsWittGraphMap (Sum.inl ())
  rw [hsWittGraphMap_injective.eq_iff]
  rcases v with v | (v | v) <;> simp [hsWittFamily]

theorem hs_local_one : {y : HSGraphPoints | hsLocalFamily y = 1} = Set.range hsPointVector := by
  ext y
  obtain ⟨v,rfl⟩ := hsWittGraphMap_surjective y
  rw [Set.mem_ofPred_eq,hs_local_family_witt]
  change hsWittFamily v = 1 ↔ ∃ c, hsWittGraphMap (Sum.inr (Sum.inl c)) = hsWittGraphMap v
  simp_rw [hsWittGraphMap_injective.eq_iff]
  rcases v with v | (v | v) <;> simp [hsWittFamily]

theorem hs_local_two : {y : HSGraphPoints | hsLocalFamily y = 2} = Set.range hsHexadVector := by
  ext y
  obtain ⟨v,rfl⟩ := hsWittGraphMap_surjective y
  rw [Set.mem_ofPred_eq,hs_local_family_witt]
  change hsWittFamily v = 2 ↔ ∃ B, hsWittGraphMap (Sum.inr (Sum.inr B)) = hsWittGraphMap v
  simp_rw [hsWittGraphMap_injective.eq_iff]
  rcases v with v | (v | v) <;> simp [hsWittFamily]

def hsSubdegree : Fin 3 → ℕ := ![1,22,77]

theorem hs_local_fiber_card (i : Fin 3) : Nat.card {y : HSGraphPoints // hsLocalFamily y = i} = hsSubdegree i := by
  fin_cases i
  · change Nat.card {y : HSGraphPoints | hsLocalFamily y = 0} = 1
    rw [hs_local_zero]; simp
  · change Nat.card {y : HSGraphPoints | hsLocalFamily y = 1} = 22
    rw [hs_local_one,Nat.card_range_of_injective hsPointVector_injective,hs_point_labels_card]
  · change Nat.card {y : HSGraphPoints | hsLocalFamily y = 2} = 77
    rw [hs_local_two,Nat.card_range_of_injective hsHexadVector_injective,hs_hexad_labels_card]

theorem hs_local_family_transitive (y z : HSGraphPoints) (he : hsLocalFamily y = hsLocalFamily z) :
    ∃ g : HSGraphStabilizer, g • y = z := by
  obtain ⟨u,rfl⟩ := hsWittGraphMap_surjective y
  obtain ⟨v,rfl⟩ := hsWittGraphMap_surjective z
  rw [hs_local_family_witt,hs_local_family_witt] at he
  rcases u with u | (u | u) <;> rcases v with v | (v | v)
  all_goals try {simp [hsWittFamily] at he}
  · exact ⟨1,by simp⟩
  · let := hs_point_labels_transitive
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq HSMathieuModel u v
    refine ⟨hsMathieuGraphEmbedding g,?_⟩
    change hsMathieu22Embedding g • hsPointVector u = hsPointVector v
    rw [← hs_point_label_equivariant,hg]
  · obtain ⟨g,hg⟩ := hs_hexad_labels_transitive u v
    refine ⟨hsMathieuGraphEmbedding g,?_⟩
    change hsMathieu22Embedding g • hsHexadVector u = hsHexadVector v
    rw [← hs_hexad_equivariant,hg]

theorem hs_stabilizer_orbit_eq_mathieu (y : HSGraphPoints) :
    MulAction.orbit HSGraphStabilizer y = MulAction.orbit HSMathieuModel y := by
  ext z
  constructor
  · rintro ⟨g,hg⟩
    obtain ⟨q,rfl⟩ := hsMathieuGraphEmbedding_bijective.surjective g
    exact ⟨q,hg⟩
  · rintro ⟨q,hq⟩
    exact ⟨hsMathieuGraphEmbedding q,hq⟩

theorem hs_stabilizer_point_orbit (c : HSPointLabels) :
    MulAction.orbit HSGraphStabilizer (hsPointVector c) = Set.range hsPointVector := by
  rw [hs_stabilizer_orbit_eq_mathieu,hs_point_family_orbit]

theorem hs_stabilizer_hexad_orbit (B : HSHexadLabels) :
    MulAction.orbit HSGraphStabilizer (hsHexadVector B) = Set.range hsHexadVector := by
  rw [hs_stabilizer_orbit_eq_mathieu,hs_hexad_family_orbit]

end Atlas.Conway
