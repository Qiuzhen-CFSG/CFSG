/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/MonomialCentralQuotient.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.LeechQuotientActions
/-!
Central signs, antipodal geometry, and faithful quotient actions for the Leech isometry group.
The proofs identify the actual kernels and transport the concrete actions through the central quotient.

Source: Gerald Höhn, `Atlas/Conway/MonomialCentralQuotient.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

def quotientPermutationEmbedding : Mathieu24CodeModel →* LeechCentralQuotient :=
  leechCentralProjection.comp permutationEmbedding

theorem permutation_ne_negation (g : Mathieu24CodeModel) :
    permutationEmbedding g ≠ negationIsometry := by
  intro he
  let a : Omega := ((0,0),0)
  have hh := congrArg (fun k : LeechIsometryGroup => (k.val (coordinateEight a)).val (g.val a)) he
  change ((permutationIsometry g).val (coordinateEight a)).val (g.val a) = _ at hh
  rw [permutation_coordinateEight,negationIsometry_apply] at hh
  change coordinateVector (g.val a) 8 (g.val a) = -coordinateVector a 8 (g.val a) at hh
  simp only [coordinateVector,Pi.single_eq_same,Pi.single_apply] at hh
  split_ifs at hh; omega

theorem quotientPermutationEmbedding_injective : Function.Injective quotientPermutationEmbedding := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro g hg
  have hh : permutationEmbedding g ∈ leechCentralSigns := by
    rw [← leechCentralProjection_kernel]
    exact hg
  rcases (leechCentralSigns_mem _).mp hh with he | he
  · have hi := permutationEmbedding_injective (he.trans permutationEmbedding.map_one.symm)
    simpa using hi
  · exact False.elim (permutation_ne_negation g he)

def quotientMonomialEmbedding : GolayMonomialGroup →* LeechCentralQuotient :=
  leechCentralProjection.comp monomialEmbedding

def quotientMonomialSubgroup : Subgroup LeechCentralQuotient := quotientMonomialEmbedding.range

def monomialCentralElement : GolayMonomialGroup :=
  SemidirectProduct.inl (Multiplicative.ofAdd (⟨allOnes,C0_le_golay allOnes_mem_C0⟩ : golay))

theorem monomialCentralElement_image : monomialEmbedding monomialCentralElement = negationIsometry := by
  exact congrArg (fun f : Multiplicative golay →* LeechIsometryGroup =>
    f (Multiplicative.ofAdd (⟨allOnes,C0_le_golay allOnes_mem_C0⟩ : golay))) monomial_inl

theorem quotientMonomialEmbedding_kernel_mem (m : GolayMonomialGroup) :
    m ∈ quotientMonomialEmbedding.ker ↔ m = 1 ∨ m = monomialCentralElement := by
  change leechCentralProjection (monomialEmbedding m) = 1 ↔ _
  rw [← MonoidHom.mem_ker,leechCentralProjection_kernel,leechCentralSigns_mem]
  constructor
  · rintro (he | he)
    · exact Or.inl (monomialEmbedding_injective (he.trans monomialEmbedding.map_one.symm))
    · exact Or.inr (monomialEmbedding_injective (he.trans monomialCentralElement_image.symm))
  · rintro (rfl | rfl)
    · exact Or.inl monomialEmbedding.map_one
    · exact Or.inr monomialCentralElement_image

theorem quotientMonomialEmbedding_kernel :
    quotientMonomialEmbedding.ker = Subgroup.zpowers monomialCentralElement := by
  apply le_antisymm
  · intro m hm
    rcases (quotientMonomialEmbedding_kernel_mem m).mp hm with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · exact Subgroup.zpowers_le.mpr ((quotientMonomialEmbedding_kernel_mem _).mpr (Or.inr rfl))

theorem quotientMonomialEmbedding_kernel_card : Nat.card quotientMonomialEmbedding.ker = 2 := by
  rw [quotientMonomialEmbedding_kernel,Nat.card_zpowers]
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply monomialEmbedding_injective
    rw [map_pow,monomialCentralElement_image,pow_two,negationIsometry_sq,map_one]
  · intro he
    apply negationIsometry_ne_one
    rw [← monomialCentralElement_image,he,map_one]

def quotientMonomialEquiv : GolayMonomialGroup ⧸ quotientMonomialEmbedding.ker ≃*
    quotientMonomialSubgroup := QuotientGroup.quotientKerEquivRange quotientMonomialEmbedding

theorem quotientMonomialSubgroup_order : Nat.card quotientMonomialSubgroup = 501397585920 := by
  have he := Subgroup.card_eq_card_quotient_mul_card_subgroup quotientMonomialEmbedding.ker
  rw [quotientMonomialEmbedding_kernel_card,
    Nat.card_congr quotientMonomialEquiv.toEquiv] at he
  have hm : Nat.card GolayMonomialGroup = 1002795171840 :=
    (Nat.card_congr monomialSubgroupEquiv.toEquiv).trans monomial_order
  rw [hm] at he
  omega

end Atlas.Conway
