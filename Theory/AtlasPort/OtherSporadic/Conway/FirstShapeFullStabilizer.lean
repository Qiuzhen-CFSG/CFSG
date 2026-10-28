/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/FirstShapeFullStabilizer.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.FirstShapeStabilizer
/-!
Minimum-vector and monomial stabilizer geometry for the concrete Leech isometry group.
The proofs identify coordinate stabilizers and combine orbit geometry with exact counting.

Source: Gerald Höhn, `Atlas/Conway/FirstShapeFullStabilizer.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem minimumPairPlus_four_mem (i j : Omega) (hij : i ≠ j) :
    (minimumPairPlus i j).val ∈ twoFourFamily 0 2 := by
  let T : OutsideSupports (∅ : Finset Omega) 2 := ⟨{i,j},by simp [hij]⟩
  let s : T.val → Bit := fun _ => 0
  have he : disjointFourVector ∅ ⟨T,s⟩ = (minimumPairPlus i j).val := by
    funext k
    simp only [disjointFourVector,signedSupport,T,s,minimumPairPlus,coordinateVector,
      Pi.add_apply,Pi.single_apply]
    split_ifs <;> simp_all; aesop
  rw [← he]
  exact disjointFourVector_mem ∅ ⟨T,s⟩

theorem firstShape_point_stabilizer_monomial (i j : Omega) (hij : i ≠ j)
    (r : leechVectorStabilizer firstShapeStabilizer (minimumPairPlus i j)) :
    r.val.val ∈ monomialSubgroup := by
  have hx := firstShape_point_orbit_mem i j hij _ (MulAction.mem_orbit _ r)
  have hp := four_orthogonal_partition i j hij _ hx.1 hx.2
  rcases hp with (hy | hy) | hz
  · exact minimumPair_fixer_mem_monomial r.val.val i j r.prop hy
  · change r.val.val.val (minimumPairMinus i j) = -minimumPairMinus i j at hy
    obtain ⟨s,hs⟩ := monomial_pair_sign_swap i j hij
    have hplus : (s.val.val*r.val.val).val (minimumPairPlus i j) = minimumPairPlus i j := by
      change s.val.val.val (r.val.val.val (minimumPairPlus i j)) = _
      rw [leechVectorStabilizer_fixes,leechVectorStabilizer_fixes]
    have hminus : (s.val.val*r.val.val).val (minimumPairMinus i j) = minimumPairMinus i j := by
      change s.val.val.val (r.val.val.val (minimumPairMinus i j)) = _
      rw [hy,map_neg,hs,neg_neg]
    have hm := minimumPair_fixer_mem_monomial (s.val.val*r.val.val) i j hplus hminus
    have hh := monomialSubgroup.mul_mem (monomialSubgroup.inv_mem s.val.prop) hm
    simpa only [inv_mul_cancel_left] using hh
  · exact (firstShape_no_disjoint_fusion i j hij r hz).elim

theorem firstShapeStabilizer_eq_monomial : firstShapeStabilizer = monomialSubgroup := by
  apply le_antisymm _ monomial_le_firstShapeStabilizer
  intro g hg
  let i : Omega := ((0,0),0)
  let j : Omega := ((0,0),1)
  have hij : i ≠ j := by decide
  let x := minimumPairPlus i j
  have hx : x.val ∈ twoFourFamily 0 2 := minimumPairPlus_four_mem i j hij
  have hgx : (g.val x).val ∈ twoFourFamily 0 2 := (hg x).mpr hx
  obtain ⟨m,hm⟩ := monomial_four_minimum_transitive (g.val x) x hgx hx
  let n := monomialEmbedding m
  have hn : n ∈ monomialSubgroup := ⟨m,rfl⟩
  let r : leechVectorStabilizer firstShapeStabilizer x :=
    ⟨⟨n*g,firstShapeStabilizer.mul_mem (monomial_le_firstShapeStabilizer hn) hg⟩,hm⟩
  have hr := firstShape_point_stabilizer_monomial i j hij r
  have hmem := monomialSubgroup.mul_mem (monomialSubgroup.inv_mem hn) hr
  simpa only [r,inv_mul_cancel_left] using hmem

end Atlas.Conway
