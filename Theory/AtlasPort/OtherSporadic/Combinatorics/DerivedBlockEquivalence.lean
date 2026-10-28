/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Combinatorics/DerivedBlockEquivalence.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Combinatorics.DerivedSteiner

/-!
# DerivedBlockEquivalence

Blocks containing a marked point correspond to blocks of the derived design.
Erasure and reinsertion give the explicit inverse maps.

Source: Gerald Höhn, ATLAS, `Atlas/Combinatorics/DerivedBlockEquivalence.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

noncomputable section
namespace Atlas.Combinatorics
attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

def derivedBlocksThroughEquiv (blocks : Finset (Finset α)) (a : α) :
    {B // B ∈ derivedBlocks blocks a} ≃ {O // O ∈ blocks ∧ a ∈ O} where
  toFun B := ⟨insert a (complementBlockLift a B.val),
    (derivedBlocks_mem blocks a B.val).mp B.prop,Finset.mem_insert_self _ _⟩
  invFun O := ⟨complementBlockRestrict a O.val,by
    rw [derivedBlocks_mem,complementBlock_restore a O.val O.prop.2]
    exact O.prop.1⟩
  left_inv B := by
    apply Subtype.ext
    ext x
    simp [complementBlockRestrict,complementBlockLift,x.prop]
  right_inv O := Subtype.ext (complementBlock_restore a O.val O.prop.2)

theorem derivedBlocksThroughEquiv_other_mem (blocks : Finset (Finset α)) (a : α)
    (b : PointComplement a) (B : {B // B ∈ derivedBlocks blocks a}) :
    b.val ∈ (derivedBlocksThroughEquiv blocks a B).val ↔ b ∈ B.val := by
  change b.val ∈ insert a (complementBlockLift a B.val) ↔ _
  simp [complementBlockLift,b.prop]

theorem derivedBlocks_through_card (blocks : Finset (Finset α)) (a : α) :
    (derivedBlocks blocks a).card = (blocks.filter (fun O => a ∈ O)).card := by
  have he := Nat.card_congr (derivedBlocksThroughEquiv blocks a)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe,Fintype.card_subtype,
    Finset.filter_and,Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.inter_filter,Finset.inter_univ] using he

end Atlas.Combinatorics
