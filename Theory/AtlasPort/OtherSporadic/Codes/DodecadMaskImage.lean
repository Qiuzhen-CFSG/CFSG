/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.DodecadMaskKernel
public import Mathlib.LinearAlgebra.Quotient.Card

/-!
# DodecadMaskImage

The polar mask map has the full space of even masks as its image. Its two-element kernel
gives an eight-element image, and equal cardinalities prove surjectivity; this connects
masks of the same parity.

Source: `Atlas/Codes/DodecadMaskImage.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open scoped BigOperators

abbrev DodecadMaskPositions (i : HexIndex) (h : hexZeroCoordinate i) :=
  {k : HexIndex // h.val.val k ≠ 0}

theorem dodecadMaskPositions_card (i : HexIndex) (h : hexZeroCoordinate i) (hh : h ≠ 0) :
    Nat.card (DodecadMaskPositions i h) = 4 := by
  classical
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, hammingNorm, DodecadMaskPositions] using
    hexZeroCoordinate_nonzero_weight i h hh

def dodecadEvenMasks (i : HexIndex) (h : hexZeroCoordinate i) :
    Submodule Bit (DodecadMaskPositions i h → Bit) :=
  LinearMap.ker
    ({ toFun := fun r => ∑ k, r k
       map_add' := by intros; simp [Finset.sum_add_distrib]
       map_smul' := by intros; simp [Finset.mul_sum] } :
      (DodecadMaskPositions i h → Bit) →ₗ[Bit] Bit)

theorem dodecadMaskMap_even (i : HexIndex) (h t : hexZeroCoordinate i) :
    dodecadMaskMap i h t ∈ dodecadEvenMasks i h := by
  classical
  change (∑ k : DodecadMaskPositions i h, polar (h.val.val k) (t.val.val k)) = 0
  have he : (∑ k : DodecadMaskPositions i h, polar (h.val.val k) (t.val.val k)) =
      ∑ k : HexIndex, polar (h.val.val k) (t.val.val k) := by
    calc
      _ = ∑ k ∈ Finset.univ.filter (fun k => h.val.val k ≠ 0),
          polar (h.val.val k) (t.val.val k) := by
        symm
        apply Finset.sum_subtype
        intro k
        simp
      _ = _ := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : h.val.val k = 0 <;> simp [hk]
  rw [he]
  have ht : t.val.val ∈ dual hexacode := hexacode_selfDual ▸ t.val.prop
  exact ht h.val.val h.val.prop

theorem dodecadMaskMap_kernel_card (i : HexIndex) (h : hexZeroCoordinate i) (hh : h ≠ 0) :
    Nat.card (dodecadMaskMap i h).ker = 2 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have he : Finset.univ.filter (fun t => t ∈ (dodecadMaskMap i h).ker) = {0, h} := by
    ext t
    simp [LinearMap.mem_ker, dodecadMaskMap_kernel i h hh]
  rw [he, Finset.card_pair hh.symm]

theorem dodecadMaskMap_image_card (i : HexIndex) (h : hexZeroCoordinate i) (hh : h ≠ 0) :
    Nat.card (dodecadMaskMap i h).range = 8 := by
  have hc := (dodecadMaskMap i h).ker.card_eq_card_quotient_mul_card
  rw [hexZeroCoordinate_card, dodecadMaskMap_kernel_card i h hh,
    Nat.card_congr (dodecadMaskMap i h).quotKerEquivRange.toEquiv] at hc
  omega

theorem dodecadEvenMasks_card (i : HexIndex) (h : hexZeroCoordinate i) (hh : h ≠ 0) :
    Nat.card (dodecadEvenMasks i h) = 8 := by
  classical
  let e : DodecadMaskPositions i h ≃ Fin 4 :=
    Fintype.equivFinOfCardEq (by simpa only [← Nat.card_eq_fintype_card] using
      (dodecadMaskPositions_card i h hh))
  let E : dodecadEvenMasks i h ≃ parityCode 3 :=
    { toFun := fun r => ⟨fun k => r.val (e.symm k), (parityCode_mem 3 _).mpr (by
        rw [e.symm.sum_comp]
        exact r.prop)⟩
      invFun := fun r => ⟨fun k => r.val (e k), by
        change (∑ k, r.val (e k)) = 0
        rw [e.sum_comp]
        exact (parityCode_mem 3 _).mp r.prop⟩
      left_inv := by intro r; apply Subtype.ext; funext k; simp
      right_inv := by intro r; apply Subtype.ext; funext k; simp }
  rw [Nat.card_congr E, parityCode_card]
  rfl

theorem dodecadMaskMap_range (i : HexIndex) (h : hexZeroCoordinate i) (hh : h ≠ 0) :
    (dodecadMaskMap i h).range = dodecadEvenMasks i h := by
  classical
  have hle : (dodecadMaskMap i h).range ≤ dodecadEvenMasks i h := by
    rintro _ ⟨t, rfl⟩
    exact dodecadMaskMap_even i h t
  apply SetLike.coe_injective
  apply Set.eq_of_subset_of_card_le hle
  simp only [← Nat.card_eq_fintype_card]
  change Nat.card (dodecadEvenMasks i h) ≤ Nat.card (dodecadMaskMap i h).range
  rw [
    dodecadMaskMap_image_card i h hh, dodecadEvenMasks_card i h hh]

theorem dodecadMaskMap_connect_masks (i : HexIndex) (h : hexZeroCoordinate i) (hh : h ≠ 0)
    (r s : DodecadMaskPositions i h → Bit) (he : (∑ k, r k) = ∑ k, s k) :
    ∃ t : hexZeroCoordinate i, r + dodecadMaskMap i h t = s := by
  have hm : s - r ∈ dodecadEvenMasks i h := by
    change (∑ k, (s - r) k) = 0
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, he, sub_self]
  rw [← dodecadMaskMap_range i h hh] at hm
  obtain ⟨t, ht⟩ := hm
  exact ⟨t, by rw [ht]; abel⟩

theorem dodecad_parameter_mask_odd (i : HexIndex) (h : hexZeroCoordinate i) (hh : h ≠ 0)
    (r : P6) (ri : r.val (hexIndexEquiv i) = 1)
    (rz : ∀ k, k ≠ i → h.val.val k = 0 → r.val (hexIndexEquiv k) = 0) :
    (∑ k : DodecadMaskPositions i h, r.val (hexIndexEquiv k)) = 1 := by
  have _ := hh
  classical
  have hi : h.val.val i = 0 := h.prop
  have hs : (∑ k : DodecadMaskPositions i h, r.val (hexIndexEquiv k)) =
      ∑ k : HexIndex, if h.val.val k ≠ 0 then r.val (hexIndexEquiv k) else 0 := by
    rw [← Finset.sum_filter]
    symm
    apply Finset.sum_subtype
    intro k
    simp
  have he (k : HexIndex) : r.val (hexIndexEquiv k) =
      (if k = i then 1 else 0) + (if h.val.val k ≠ 0 then r.val (hexIndexEquiv k) else 0) := by
    by_cases hki : k = i
    · subst k; simp [hi,ri]
    by_cases hk : h.val.val k = 0 <;> simp [hki,hk,rz k hki]
  have hall := congrArg (fun f : HexIndex → Bit => ∑ k, f k) (funext he)
  rw [Finset.sum_add_distrib, ← hs, hexIndexEquiv.sum_comp,
    (parityCode_mem 5 _).mp r.prop] at hall
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hall
  have hb : ∀ x : Bit, 0 = 1 + x → x = 1 := by decide
  exact hb _ hall

end Atlas.Codes
