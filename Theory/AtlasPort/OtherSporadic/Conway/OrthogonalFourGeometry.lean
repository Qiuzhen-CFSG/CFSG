/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/OrthogonalFourGeometry.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.DisjointFourCount
/-!
Orthogonal minimum-vector geometry in the concrete Leech lattice.
The proofs use coordinate shapes, Golay support counts, and stabilizer orbit transport.

Source: Gerald Höhn, `Atlas/Conway/OrthogonalFourGeometry.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem minimumPairPlus_dot (i j : Omega) (x : IntegerCoordinates) :
    integerDot (minimumPairPlus i j).val x = 4 * (x i + x j) := by
  simp [minimumPairPlus,integerDot,coordinateVector,Pi.single_apply,add_mul,ite_mul,
    Finset.sum_add_distrib,mul_add]

theorem four_orthogonal_nonzero_pair (i j : Omega) (hij : i ≠ j) (x : leech)
    (hx : x.val ∈ twoFourFamily 0 2)
    (ho : integerDot (minimumPairPlus i j).val x.val = 0) (hi : x.val i ≠ 0) :
    x = minimumPairMinus i j ∨ x = -minimumPairMinus i j := by
  have he : x.val i + x.val j = 0 := by rw [minimumPairPlus_dot] at ho; omega
  have hj : x.val j ≠ 0 := by omega
  obtain ⟨T,hT,s,hs⟩ := minimum_four_parameterization x hx
  have hiT : i ∈ T := by
    by_contra hn
    exact hi (by rw [hs]; simp [signedSupport,hn])
  have hjT : j ∈ T := by
    by_contra hn
    exact hj (by rw [hs]; simp [signedSupport,hn])
  have hTpair : T = {i,j} := (Finset.eq_of_subset_of_card_le
    (Finset.insert_subset hiT (Finset.singleton_subset_iff.mpr hjT)) (by simp [hT,hij])).symm
  have hxi : x.val i = 4 ∨ x.val i = -4 := by
    rw [hs]
    simp only [signedSupport,dif_pos hiT]
    split_ifs <;> norm_num
  have hz (k : Omega) (hki : k ≠ i) (hkj : k ≠ j) : x.val k = 0 := by
    rw [hs]
    have hk : k ∉ T := by simp [hTpair,hki,hkj]
    simp [signedSupport,hk]
  rcases hxi with hxi | hxi
  · left
    apply Subtype.ext
    funext k
    by_cases hki : k = i
    · subst k; simp [minimumPairMinus,coordinateVector,hij,hxi]
    · by_cases hkj : k = j
      · subst k
        have hxj : x.val j = -4 := by omega
        simp [minimumPairMinus,coordinateVector,hki,hxj]
      · simp [minimumPairMinus,coordinateVector,hki,hkj,hz k hki hkj]
  · right
    apply Subtype.ext
    funext k
    change x.val k = -((minimumPairMinus i j).val k)
    by_cases hki : k = i
    · subst k; simp [minimumPairMinus,coordinateVector,hij,hxi]
    · by_cases hkj : k = j
      · subst k
        have hxj : x.val j = 4 := by omega
        simp [minimumPairMinus,coordinateVector,hki,hxj]
      · simp [minimumPairMinus,coordinateVector,hki,hkj,hz k hki hkj]

theorem four_orthogonal_partition (i j : Omega) (hij : i ≠ j) (x : leech)
    (hx : x.val ∈ twoFourFamily 0 2)
    (ho : integerDot (minimumPairPlus i j).val x.val = 0) :
    (x = minimumPairMinus i j ∨ x = -minimumPairMinus i j) ∨
      (x.val i = 0 ∧ x.val j = 0) := by
  by_cases hi : x.val i = 0
  · right
    rw [minimumPairPlus_dot,hi] at ho
    exact ⟨hi,by omega⟩
  · exact Or.inl (four_orthogonal_nonzero_pair i j hij x hx ho hi)

end Atlas.Conway
