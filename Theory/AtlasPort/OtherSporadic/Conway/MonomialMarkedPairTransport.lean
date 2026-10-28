/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/MonomialMarkedPairTransport.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.MarkedSupportSigns
public import Theory.AtlasPort.OtherSporadic.Conway.OddPointStabilizerOrbits
/-!
Minimum-vector and monomial stabilizer geometry for the concrete Leech isometry group.
The proofs identify coordinate stabilizers and combine orbit geometry with exact counting.

Source: Gerald Höhn, `Atlas/Conway/MonomialMarkedPairTransport.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem monomial_sign_zero_of_coordinate_match (m : GolayMonomialGroup) (x y : leech)
    (hm : (monomialEmbedding m).val x = y) (i : Omega)
    (hx : x.val (m.right.val.symm i) = y.val i) (hy : y.val i ≠ 0) : m.left.toAdd.val i = 0 := by
  have he := congrArg (fun z : leech => z.val i) hm
  rw [monomialEmbedding_apply] at he
  by_contra hn
  rw [if_neg hn,hx] at he
  exact hy (by omega)

theorem monomial_fixes_pair_plus (m : GolayMonomialGroup) (i j : Omega) (hij : i ≠ j)
    (hp : (m.right.val i = i ∧ m.right.val j = j) ∨ (m.right.val i = j ∧ m.right.val j = i))
    (hi : m.left.toAdd.val i = 0) (hj : m.left.toAdd.val j = 0) :
    (monomialEmbedding m).val (minimumPairPlus i j) = minimumPairPlus i j := by
  apply Subtype.ext
  funext k
  rw [monomialEmbedding_apply]
  rcases hp with ⟨hpi,hpj⟩ | ⟨hpi,hpj⟩
  all_goals
    simp only [minimumPairPlus,coordinateVector,Pi.add_apply,Pi.single_apply,Equiv.symm_apply_eq,hpi,hpj]
    by_cases hki : k = i
    · subst k; simp [hi,hij]
    · by_cases hkj : k = j
      · subst k; simp [hj,hki]
      · simp [hki,hkj]

theorem monomial_support_transport_marked_pair (g : Mathieu24CodeModel) (k : ℤ)
    (S T : Finset Omega) (hg : permuteBlock g.val S = T) (c d : golay) (x y : leech)
    (hx : x.val = signChange c.val (constantSupportVector k S))
    (hy : y.val = signChange d.val (constantSupportVector k T))
    (i j : Omega) (hij : i ≠ j)
    (hp : (g.val i = i ∧ g.val j = j) ∨ (g.val i = j ∧ g.val j = i))
    (hxi : x.val (g.val.symm i) = y.val i) (hxj : x.val (g.val.symm j) = y.val j)
    (hyi : y.val i ≠ 0) (hyj : y.val j ≠ 0) :
    ∃ r : leechVectorStabilizer monomialSubgroup (minimumPairPlus i j), r.val.val.val x = y := by
  let m : GolayMonomialGroup := ⟨Multiplicative.ofAdd (d + golayPermutationEquiv g c),g⟩
  have hm : (monomialEmbedding m).val x = y := by
    apply Subtype.ext
    change signChange (d.val + coordinatePermutation g.val c.val) (integerPermutation g.val x.val) = y.val
    rw [hx,hy,permutation_sign_conjugation,signChange_add,signChange_involutive,
      permutation_constantSupport,hg]
  have hmi := monomial_sign_zero_of_coordinate_match m x y hm i hxi hyi
  have hmj := monomial_sign_zero_of_coordinate_match m x y hm j hxj hyj
  have hfix := monomial_fixes_pair_plus m i j hij hp hmi hmj
  exact ⟨⟨⟨monomialEmbedding m,⟨m,rfl⟩⟩,hfix⟩,hm⟩

end Atlas.Conway
