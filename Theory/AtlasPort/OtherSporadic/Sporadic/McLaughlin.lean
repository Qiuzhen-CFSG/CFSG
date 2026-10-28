/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Sporadic/McLaughlin.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.McLOrder

/-!
The concrete McLaughlin carrier, its order and compatible Conway embeddings.
The carrier is the full pointwise stabilizer of the fixed Leech triangle;
the endpoint exact sequence supplies its order and its index in Conway3.

Source: Gerald Höhn, ATLAS, `Atlas/Sporadic/McLaughlin.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definitions,
preserving source namespaces and the coordinate reductions used across modules.
-/

@[expose] public section

noncomputable section
namespace Atlas.Sporadic.McLaughlin
open Atlas.Codes Atlas.Lattices Atlas.Conway

/-- Actual pointwise stabilizer of the fixed 2-2-3 Leech triangle. -/
abbrev Model := McLModel

def vector : leech := Conway3.vector.val

def endpoint : leech := mclEndpoint

def otherEndpoint : leech := mclOtherEndpoint

def order : ℕ := 898128000

theorem finite : Finite Model := inferInstance

theorem card : Nat.card Model = order := mcl_order

theorem card_factorization : Nat.card Model = 2^7*3^6*5^3*7*11 := mcl_order_factorization

def toConway3 : Model →* Conway3.Model := (MulAction.stabilizer Conway3.Model mclEndpoint).subtype

theorem toConway3_injective : Function.Injective toConway3 := Subtype.val_injective

def embedding : Model →* LeechIsometryGroup := Conway3.embedding.comp toConway3

theorem embedding_injective : Function.Injective embedding :=
  Conway3.embedding_injective.comp toConway3_injective

def toConway1 : Model →* LeechCentralQuotient := Conway3.toConway1.comp toConway3

theorem toConway1_injective : Function.Injective toConway1 :=
  Conway3.toConway1_injective.comp toConway3_injective

abbrev PairStabilizer := McLPairStabilizer
abbrev Endpoints := McLEndpoints

def endpointPermutation := mclEndpointPermutation

theorem endpointPermutation_surjective : Function.Surjective endpointPermutation :=
  mcl_endpoint_permutation_surjective

def endpointKernelEquiv : endpointPermutation.ker ≃* Model := mclEndpointKernelEquiv

/-- The kernel inclusion preserves the actual ambient lattice isometry. -/
def toPairStabilizer : Model →* PairStabilizer :=
  endpointPermutation.ker.subtype.comp endpointKernelEquiv.symm.toMonoidHom

theorem toPairStabilizer_compatible (g : Model) : (toPairStabilizer g).val = toConway3 g := rfl

theorem toPairStabilizer_range : toPairStabilizer.range = endpointPermutation.ker := by
  ext g
  constructor
  · rintro ⟨h,rfl⟩; exact (endpointKernelEquiv.symm h).prop
  · intro hg
    exact ⟨endpointKernelEquiv ⟨g,hg⟩,congrArg Subtype.val (endpointKernelEquiv.symm_apply_apply _)⟩

theorem pair_card : Nat.card PairStabilizer = 1796256000 := mcl_pair_order

theorem endpoint_index_product : 2*Nat.card Model = Nat.card PairStabilizer := mcl_endpoint_index_product

theorem co3_index_product : 552*Nat.card Model = Nat.card Conway3.Model := mcl_co3_index_product

end Atlas.Sporadic.McLaughlin
