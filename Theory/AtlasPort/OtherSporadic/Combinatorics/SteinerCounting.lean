/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Combinatorics/SteinerCounting.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# SteinerCounting

A finite Steiner system has the expected total number of blocks.
Count pairs of a block and a t-subset of that block in two ways.

Source: Gerald Höhn, ATLAS, `Atlas/Combinatorics/SteinerCounting.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

noncomputable section
namespace Atlas.Combinatorics
open Finset

/-- Incidence double counting for a finite Steiner system. -/
theorem steiner_block_count {α : Type*} [Fintype α] (blocks : Finset (Finset α))
    (t k : ℕ) (sizes : ∀ B ∈ blocks, B.card = k)
    (unique : ∀ T : Finset α, T.card = t → ∃! B : Finset α, B ∈ blocks ∧ T ⊆ B) :
    blocks.card * k.choose t = (Fintype.card α).choose t := by
  classical
  let Incidence := Σ B : {B : Finset α // B ∈ blocks}, {T : Finset α // T ∈ B.val.powersetCard t}
  let projection : Incidence → {T : Finset α // T.card = t} :=
    fun x => ⟨x.2.val, (mem_powersetCard.mp x.2.prop).2⟩
  have hi : Function.Injective projection := by
    rintro ⟨B,T⟩ ⟨C,U⟩ h
    have ht : T.val = U.val := congrArg Subtype.val h
    have hb : B = C := by
      apply Subtype.ext
      obtain ⟨D,_,hD⟩ := unique T.val (mem_powersetCard.mp T.prop).2
      exact (hD B.val ⟨B.prop,(mem_powersetCard.mp T.prop).1⟩).trans
        (hD C.val ⟨C.prop,ht ▸ (mem_powersetCard.mp U.prop).1⟩).symm
    subst C
    have hu : T = U := Subtype.ext ht
    subst U
    rfl
  have hs : Function.Surjective projection := by
    intro T
    obtain ⟨B,⟨hB,hTB⟩,_⟩ := unique T.val T.prop
    exact ⟨⟨⟨B,hB⟩,⟨T.val,mem_powersetCard.mpr ⟨hTB,T.prop⟩⟩⟩,rfl⟩
  have hc := Fintype.card_congr (Equiv.ofBijective projection ⟨hi,hs⟩)
  have hf (B : {B : Finset α // B ∈ blocks}) :
      Fintype.card {T : Finset α // T ∈ B.val.powersetCard t} = k.choose t := by
    rw [Fintype.card_subtype]
    simp only [filter_mem_eq_inter, univ_inter, card_powersetCard, sizes B.val B.prop]
  change Fintype.card (Σ B : {B : Finset α // B ∈ blocks},
    {T : Finset α // T ∈ B.val.powersetCard t}) = _ at hc
  rw [Fintype.card_sigma] at hc
  simp only [hf, sum_const, smul_eq_mul, Fintype.card_finset_len] at hc
  simpa only [card_univ, Fintype.card_subtype, filter_mem_eq_inter, univ_inter] using hc

end Atlas.Combinatorics
