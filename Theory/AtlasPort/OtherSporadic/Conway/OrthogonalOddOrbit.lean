/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/OrthogonalOddOrbit.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalOddCoordinates
public import Theory.AtlasPort.OtherSporadic.Conway.MonomialMarkedPairTransport
public import Theory.AtlasPort.OtherSporadic.Mathieu.OrderedTripleTransport
/-!
Orthogonal minimum-vector geometry in the concrete Leech lattice.
The proofs use coordinate shapes, Golay support counts, and stabilizer orbit transport.

Source: Gerald Höhn, `Atlas/Conway/OrthogonalOddOrbit.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem odd_transport_marked_pair (g : Mathieu24CodeModel) (a b : Omega) (c d : golay)
    (hab : g.val a = b) (i j : Omega) (hij : i ≠ j)
    (hp : (g.val i = i ∧ g.val j = j) ∨ (g.val i = j ∧ g.val j = i))
    (hi : (oddMinimumVector a c).val (g.val.symm i) = (oddMinimumVector b d).val i)
    (hj : (oddMinimumVector a c).val (g.val.symm j) = (oddMinimumVector b d).val j)
    (hyi : (oddMinimumVector b d).val i ≠ 0) (hyj : (oddMinimumVector b d).val j ≠ 0) :
    ∃ r : leechVectorStabilizer monomialSubgroup (minimumPairPlus i j),
      r.val.val.val (oddMinimumVector a c) = oddMinimumVector b d := by
  let m : GolayMonomialGroup := ⟨Multiplicative.ofAdd (d + golayPermutationEquiv g c),g⟩
  have hm : (monomialEmbedding m).val (oddMinimumVector a c) = oddMinimumVector b d := by
    simpa only [hab] using monomial_odd_transport g a c d
  have hmi := monomial_sign_zero_of_coordinate_match m _ _ hm i hi hyi
  have hmj := monomial_sign_zero_of_coordinate_match m _ _ hm j hj hyj
  have hf := monomial_fixes_pair_plus m i j hij hp hmi hmj
  exact ⟨⟨⟨monomialEmbedding m,⟨m,rfl⟩⟩,hf⟩,hm⟩

theorem orthogonal_odd_minimum_transitive (i j : Omega) (hij : i ≠ j) (x y : leech)
    (hx : x.val ∈ oddNoFiveVectors 1) (hy : y.val ∈ oddNoFiveVectors 1)
    (hox : integerDot (minimumPairPlus i j).val x.val = 0)
    (hoy : integerDot (minimumPairPlus i j).val y.val = 0) :
    ∃ r : leechVectorStabilizer monomialSubgroup (minimumPairPlus i j), r.val.val.val x = y := by
  obtain ⟨a,c,rfl⟩ := odd_minimum_parameterization x hx
  obtain ⟨b,d,rfl⟩ := odd_minimum_parameterization y hy
  obtain ⟨hai,haj⟩ := orthogonal_odd_mark_outside i j a hij c hox
  obtain ⟨hbi,hbj⟩ := orthogonal_odd_mark_outside i j b hij d hoy
  have hsx : (oddMinimumVector a c).val i + (oddMinimumVector a c).val j = 0 := by
    rw [minimumPairPlus_dot] at hox; omega
  have hsy : (oddMinimumVector b d).val i + (oddMinimumVector b d).val j = 0 := by
    rw [minimumPairPlus_dot] at hoy; omega
  have hxi := oddMinimumVector_off_mark a i c hai.symm
  have hyi := oddMinimumVector_off_mark b i d hbi.symm
  have hyj := oddMinimumVector_off_mark b j d hbj.symm
  have hyi0 : (oddMinimumVector b d).val i ≠ 0 := by omega
  have hyj0 : (oddMinimumVector b d).val j ≠ 0 := by omega
  have hvals : (oddMinimumVector a c).val i = (oddMinimumVector b d).val i ∨
      (oddMinimumVector a c).val j = (oddMinimumVector b d).val i := by omega
  rcases hvals with hv | hv
  · obtain ⟨g,hgi,hgj,hga⟩ := mathieu24_ordered_triple_transport i j a i j b hij hai haj hij hbi hbj
    have hgi' : g.val.symm i = i := by rw [Equiv.symm_apply_eq]; exact hgi.symm
    have hgj' : g.val.symm j = j := by rw [Equiv.symm_apply_eq]; exact hgj.symm
    exact odd_transport_marked_pair g a b c d hga i j hij (Or.inl ⟨hgi,hgj⟩)
      (by rwa [hgi']) (by rw [hgj']; omega) hyi0 hyj0
  · obtain ⟨g,hgi,hgj,hga⟩ := mathieu24_ordered_triple_transport i j a j i b hij hai haj hij.symm hbj hbi
    have hgi' : g.val.symm i = j := by rw [Equiv.symm_apply_eq]; exact hgj.symm
    have hgj' : g.val.symm j = i := by rw [Equiv.symm_apply_eq]; exact hgi.symm
    exact odd_transport_marked_pair g a b c d hga i j hij (Or.inr ⟨hgi,hgj⟩)
      (by rwa [hgi']) (by rw [hgj']; omega) hyi0 hyj0

end Atlas.Conway
