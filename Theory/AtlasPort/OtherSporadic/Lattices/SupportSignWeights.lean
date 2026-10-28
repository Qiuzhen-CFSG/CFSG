/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/SupportSignWeights.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Proof syntax and simplifier arguments are adjusted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.SupportSigns
public import Theory.AtlasPort.OtherSporadic.Codes.BinaryCounting

/-!
Counts of binary words of fixed weight, including a prescribed zero coordinate.
The support equivalence identifies these words with subsets of a finite set or of a coordinate complement.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem binary_weight_count_fintype (α : Type*) [Fintype α] [DecidableEq α] (k : ℕ) :
    Nat.card {s : α → Bit // hammingNorm s = k} = (Fintype.card α).choose k := by
  let e : {s : α → Bit // hammingNorm s = k} ≃ {T : Finset α // T.card = k} :=
    Equiv.subtypeEquiv binarySupportEquiv (fun _ => Iff.rfl)
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_finset_len]

def binaryWeightZeroEquiv (α : Type*) [Fintype α] [DecidableEq α] (a : α) (k : ℕ) :
    {s : α → Bit // s a = 0 ∧ hammingNorm s = k} ≃
      {T : Finset α // T ∈ (Finset.univ.erase a).powersetCard k} :=
  Equiv.ofBijective (fun s => ⟨support s.val,by
    rw [Finset.mem_powersetCard]
    refine ⟨?_,s.prop.2⟩
    intro i hi
    have hn : i ≠ a := by intro he; subst i; simp [support,s.prop.1] at hi
    simp [hn]⟩) ⟨by
      intro s t h
      exact Subtype.ext (binarySupportEquiv.injective (congrArg Subtype.val h)),by
      intro T
      obtain ⟨hT,hcard⟩ := Finset.mem_powersetCard.mp T.prop
      have ha : a ∉ T.val := by intro ha; simpa using hT ha
      refine ⟨⟨binarySupportEquiv.symm T.val,?_,?_⟩,?_⟩
      · simp [binarySupportEquiv,ha]
      · change (support (binarySupportEquiv.symm T.val)).card = k
        rw [show support (binarySupportEquiv.symm T.val) = T.val from binarySupportEquiv.apply_symm_apply T.val]
        exact hcard
      · exact Subtype.ext (binarySupportEquiv.apply_symm_apply T.val)⟩

theorem binary_weight_zero_count (α : Type*) [Fintype α] [DecidableEq α] (a : α) (k : ℕ) :
    Nat.card {s : α → Bit // s a = 0 ∧ hammingNorm s = k} =
      (Fintype.card α-1).choose k := by
  rw [Nat.card_congr (binaryWeightZeroEquiv α a k),Nat.card_eq_fintype_card,Fintype.card_coe,
    Finset.card_powersetCard,Finset.card_erase_of_mem (Finset.mem_univ a),Finset.card_univ]

end Atlas.Lattices
