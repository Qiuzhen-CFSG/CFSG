/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/MinimalOddOrbit.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.MonomialOrder
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechOddShells
public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetTransitivity
/-!
Minimum-vector and monomial stabilizer geometry for the concrete Leech isometry group.
The proofs identify coordinate stabilizers and combine orbit geometry with exact counting.

Source: Gerald Höhn, `Atlas/Conway/MinimalOddOrbit.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

def oddMinimumVector (a : Omega) (c : golay) : leech :=
  ⟨signedOddProfile {a} ∅ c,signedOddProfile_mem _ _ (by simp) c⟩

theorem permutation_odd_singleton (g : Mathieu24CodeModel) (a : Omega) :
    integerPermutation g.val (oddProfileBase {a} ∅) = oddProfileBase {g.val a} ∅ := by
  funext i
  change oddProfileBase {a} ∅ (g.val.symm i) = _
  simp only [oddProfileBase,Finset.mem_singleton,Finset.notMem_empty,ite_false,add_zero,
    Equiv.symm_apply_eq]

theorem monomial_odd_transport (g : Mathieu24CodeModel) (a : Omega) (c d : golay) :
    (monomialEmbedding ⟨Multiplicative.ofAdd (d + golayPermutationEquiv g c),g⟩).val
      (oddMinimumVector a c) = oddMinimumVector (g.val a) d := by
  apply Subtype.ext
  change signChange (d.val + coordinatePermutation g.val c.val)
    (integerPermutation g.val (signChange c.val (oddProfileBase {a} ∅))) = _
  rw [permutation_sign_conjugation,signChange_add,signChange_involutive,permutation_odd_singleton]
  rfl

theorem monomial_odd_minimum_transitive (a b : Omega) (c d : golay) :
    ∃ m : GolayMonomialGroup, (monomialEmbedding m).val (oddMinimumVector a c) =
      oddMinimumVector b d := by
  obtain ⟨g,hg⟩ := golay_coordinate_transitive a b
  refine ⟨⟨Multiplicative.ofAdd (d + golayPermutationEquiv g c),g⟩,?_⟩
  simpa [hg] using monomial_odd_transport g a c d

theorem odd_minimum_parameterization (x : leech) (hx : x.val ∈ oddNoFiveVectors 1) :
    ∃ a c, oddMinimumVector a c = x := by
  obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hx
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp p.1.prop
  refine ⟨a,p.2,?_⟩
  apply Subtype.ext
  change signedOddProfile {a} ∅ p.2 = x.val
  simpa [noFiveVector,ha] using hp

end Atlas.Conway
