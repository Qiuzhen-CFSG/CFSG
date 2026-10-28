/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/OrthogonalPairSigns.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalFourGeometry
public import Theory.AtlasPort.OtherSporadic.Conway.MonomialCentralQuotient
/-!
Orthogonal minimum-vector geometry in the concrete Leech lattice.
The proofs use coordinate shapes, Golay support counts, and stabilizer orbit transport.

Source: Gerald Höhn, `Atlas/Conway/OrthogonalPairSigns.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem minimumPairMinus_four_mem (i j : Omega) (hij : i ≠ j) :
    (minimumPairMinus i j).val ∈ twoFourFamily 0 2 := by
  let T : OutsideSupports (∅ : Finset Omega) 2 := ⟨{i,j},by simp [hij]⟩
  let s : T.val → Bit := fun k => if k.val = i then 0 else 1
  have he : disjointFourVector ∅ ⟨T,s⟩ = (minimumPairMinus i j).val := by
    funext k
    simp only [disjointFourVector,signedSupport,T,s,minimumPairMinus,coordinateVector,
      Pi.sub_apply,Pi.single_apply]
    split_ifs <;> simp_all; aesop
  rw [← he]
  exact disjointFourVector_mem ∅ ⟨T,s⟩

theorem neg_minimumPairMinus_four_mem (i j : Omega) (hij : i ≠ j) :
    (-minimumPairMinus i j).val ∈ twoFourFamily 0 2 := by
  have h := monomial_twoFour_invariant monomialCentralElement (minimumPairMinus i j) 0 2
    (minimumPairMinus_four_mem i j hij)
  rwa [monomialCentralElement_image,negationIsometry_apply] at h

theorem minimumPairMinus_ne_neg (i j : Omega) (hij : i ≠ j) :
    minimumPairMinus i j ≠ -minimumPairMinus i j := by
  intro he
  have h := congrArg (fun x : leech => x.val i) he
  change (minimumPairMinus i j).val i = -((minimumPairMinus i j).val i) at h
  norm_num [minimumPairMinus,coordinateVector,Pi.single_apply,hij] at h

theorem permutation_minimumPair (g : Mathieu24CodeModel) (i j : Omega) :
    (permutationEmbedding g).val (minimumPairPlus i j) = minimumPairPlus (g.val i) (g.val j) ∧
    (permutationEmbedding g).val (minimumPairMinus i j) = minimumPairMinus (g.val i) (g.val j) := by
  constructor <;> apply Subtype.ext <;> funext k
  all_goals simp [permutationEmbedding,permutationIsometry,integerPermutation,minimumPairPlus,
    minimumPairMinus,coordinateVector,Pi.single_apply,Equiv.symm_apply_eq]

theorem monomial_pair_sign_swap (i j : Omega) (hij : i ≠ j) :
    ∃ g : leechVectorStabilizer monomialSubgroup (minimumPairPlus i j),
      g.val.val.val (minimumPairMinus i j) = -minimumPairMinus i j := by
  have ht : MulAction.IsMultiplyPretransitive Mathieu24CodeModel Omega 2 := by
    let := mathieu24_five_transitive
    exact MulAction.isMultiplyPretransitive_of_le (by decide : 2 ≤ 5)
      (by norm_num [Omega,HexIndex])
  obtain ⟨g,hgi,hgj⟩ := (MulAction.is_two_pretransitive_iff.mp ht) hij hij.symm
  have hN : permutationEmbedding g ∈ monomialSubgroup :=
    ⟨SemidirectProduct.inr g,congrArg (fun f => f g) monomial_inr⟩
  have hplus : minimumPairPlus j i = minimumPairPlus i j := by
    apply Subtype.ext
    exact add_comm _ _
  have hminus : minimumPairMinus j i = -minimumPairMinus i j := by
    apply Subtype.ext
    exact (neg_sub _ _).symm
  have hs := permutation_minimumPair g i j
  rw [show g.val i = j from hgi,show g.val j = i from hgj,hplus,hminus] at hs
  exact ⟨⟨⟨permutationEmbedding g,hN⟩,hs.1⟩,hs.2⟩

def PairSignClass (i j : Omega) :=
  {x : leech // x = minimumPairMinus i j ∨ x = -minimumPairMinus i j}

theorem pairSignClass_card (i j : Omega) (hij : i ≠ j) :
    Nat.card (PairSignClass i j) = 2 := by
  have he : PairSignClass i j ≃ {x // x ∈ ({minimumPairMinus i j,-minimumPairMinus i j} : Finset leech)} :=
    Equiv.subtypeEquivRight (fun x => by simp)
  rw [Nat.card_congr he,Nat.card_eq_fintype_card,Fintype.card_coe,
    Finset.card_pair (minimumPairMinus_ne_neg i j hij)]

end Atlas.Conway
