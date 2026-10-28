/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.Dodecads
public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeZeroFibers
public import Theory.AtlasPort.OtherSporadic.Codes.GolayRecovery

/-!
# DodecadParameters

A dodecad containing a tetrad has a unique even Golay encoding with a nonzero hexacode
component. Block parity and weight determine the vanishing coordinates and mask
restrictions, and the converse reconstructs its support.

Source: `Atlas/Codes/DodecadParameters.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open scoped BigOperators
open Finset

theorem c0Encoder_contains_tetrad (h : hexacode) (r : P6) (i : HexIndex) :
    tetrad i ⊆ support (c0Encoder (h, r)) ↔ h.val i = 0 ∧ r.val (hexIndexEquiv i) = 1 := by
  have local_test : ∀ u : K, ∀ b : Bit,
      (∀ k : Fin 4, j u k + b ≠ 0) ↔ u = 0 ∧ b = 1 := by decide
  rw [← local_test]
  constructor
  · intro ht k
    exact (mem_filter.mp (ht ((mem_tetrad (i,k) i).mpr rfl))).2
  · intro ht p hp
    have he := (mem_tetrad p i).mp hp
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    change j (h.val p.1) p.2 + r.val (hexIndexEquiv p.1) ≠ 0
    rw [he]
    exact ht p.2

theorem dodecad_through_tetrad_even (w : golay) (i : HexIndex)
    (hi : tetrad i ⊆ support w.val) : w.val ∈ C0 := by
  obtain ⟨⟨h,r,ε⟩,hw⟩ := w.prop
  have hp : blockParity w.val i = 0 := by
    have he : (fun k : Fin 4 => w.val (i,k)) = fun _ => 1 := by
      funext k
      have hn := (mem_filter.mp (hi ((mem_tetrad (i,k) i).mpr rfl))).2
      have hb : ∀ x : Bit, x ≠ 0 → x = 1 := by decide
      exact hb _ hn
    change (∑ k : Fin 4, w.val (i,k)) = 0
    rw [he]
    decide
  rw [← hw, golayEncoder_blockParity] at hp
  exact ⟨(h,r), by simpa [golayEncoder, hp] using hw⟩

theorem dodecad_parameters_nonzero (h : hexacode) (r : P6)
    (hw : hammingNorm (c0Encoder (h,r)) = 12) : h ≠ 0 := by
  intro hh
  subst h
  have hc := c0_weight_zero_count 3
  norm_num [Nat.choose] at hc
  have hn : Nonempty {r : P6 // hammingNorm (c0Encoder (0,r)) = 12} := ⟨⟨r,hw⟩⟩
  have hp := Nat.card_pos (α := {r : P6 // hammingNorm (c0Encoder (0,r)) = 12})
  have hz : Nat.card {r : P6 // hammingNorm (c0Encoder (0,r)) = 12} = 0 := by
    simpa only [Nat.card_eq_fintype_card] using hc
  omega

theorem dodecad_parameters_empty (h : hexacode) (r : P6) (i j : HexIndex)
    (hw : hammingNorm (c0Encoder (h,r)) = 12)
    (hi : h.val i = 0) (ri : r.val (hexIndexEquiv i) = 1)
    (hji : j ≠ i) (hj : h.val j = 0) : r.val (hexIndexEquiv j) = 0 := by
  have hd : support (c0Encoder (h,r)) ∈ dodecads :=
    (dodecads_mem _).mpr ⟨⟨_, C0_le_golay ⟨(h,r),rfl⟩⟩, hw, rfl⟩
  have hn := dodecad_not_two_tetrads _ hd i j hji.symm
    ((c0Encoder_contains_tetrad h r i).mpr ⟨hi,ri⟩)
  have he : r.val (hexIndexEquiv j) ≠ 1 := fun hr =>
    hn ((c0Encoder_contains_tetrad h r j).mpr ⟨hj,hr⟩)
  have hb : ∀ x : Bit, x ≠ 1 → x = 0 := by decide
  exact hb _ he

theorem dodecad_parameters_exist (w : golay) (hw : hammingNorm w.val = 12)
    (i : HexIndex) (hi : tetrad i ⊆ support w.val) :
    ∃ h : hexZeroCoordinate i, ∃ r : P6, h ≠ 0 ∧
      c0Encoder (h.val,r) = w.val ∧ r.val (hexIndexEquiv i) = 1 ∧
      ∃! j : HexIndex, j ≠ i ∧ h.val.val j = 0 ∧ r.val (hexIndexEquiv j) = 0 := by
  obtain ⟨⟨h,r⟩,he⟩ := dodecad_through_tetrad_even w i hi
  have hs := (c0Encoder_contains_tetrad h r i).mp (he.symm ▸ hi)
  let u : hexZeroCoordinate i := ⟨h,hs.1⟩
  have hu : u ≠ 0 := fun hz => dodecad_parameters_nonzero h r (he.symm ▸ hw)
    (congrArg Subtype.val hz)
  obtain ⟨j, hj, huniq⟩ := hexZeroCoordinate_unique_other_zero i u hu
  refine ⟨u,r,hu,he,hs.2,j,⟨hj.1,hj.2,?_⟩,?_⟩
  · exact dodecad_parameters_empty h r i j (he.symm ▸ hw) hs.1 hs.2 hj.1 hj.2
  · intro k hk
    exact huniq k ⟨hk.1,hk.2.1⟩

theorem dodecad_parameters_converse (i : HexIndex) (h : hexZeroCoordinate i) (hh : h ≠ 0)
    (r : P6) (ri : r.val (hexIndexEquiv i) = 1)
    (j : HexIndex) (hji : j ≠ i) (hj : h.val.val j = 0)
    (rj : r.val (hexIndexEquiv j) = 0) :
    support (c0Encoder (h.val,r)) ∈ dodecads ∧
      tetrad i ⊆ support (c0Encoder (h.val,r)) := by
  have hi : h.val.val i = 0 := h.prop
  obtain ⟨j₀,hj₀,huniq⟩ := hexZeroCoordinate_unique_other_zero i h hh
  have hj₀j : j₀ = j := (huniq j ⟨hji,hj⟩).symm
  subst j₀
  have hf : Finset.univ.filter (fun k : Fin 6 =>
      h.val.val (hexIndexEquiv.symm k) = 0 ∧ r.val k ≠ 0) = {hexIndexEquiv i} := by
    ext k
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨hk,hr⟩
      by_cases hki : hexIndexEquiv.symm k = i
      · exact (hexIndexEquiv.symm_apply_eq).mp hki
      · have he := huniq (hexIndexEquiv.symm k) ⟨hki,hk⟩
        have hkj : k = hexIndexEquiv j := (hexIndexEquiv.symm_apply_eq).mp he
        exact False.elim (hr (hkj ▸ rj))
    · rintro rfl
      simp [hi,ri]
  refine ⟨(dodecads_mem _).mpr ⟨⟨_,C0_le_golay ⟨(h.val,r),rfl⟩⟩,?_,rfl⟩,
    (c0Encoder_contains_tetrad h.val r i).mpr ⟨hi,ri⟩⟩
  rw [c0Encoder_weight_formula, hexZeroCoordinate_nonzero_weight i h hh, hf]
  simp

theorem dodecad_parameters_unique (h h' : hexacode) (r r' : P6)
    (he : support (c0Encoder (h,r)) = support (c0Encoder (h',r'))) :
    h = h' ∧ r = r' := by
  have he' : c0Equiv (h,r) = c0Equiv (h',r') := Subtype.ext (support_injective he)
  exact Prod.mk.inj (c0Equiv.injective he')

theorem dodecad_parameters_block_shape (i : HexIndex) (h : hexZeroCoordinate i) (hh : h ≠ 0)
    (r : P6) (ri : r.val (hexIndexEquiv i) = 1) (j : HexIndex) (hji : j ≠ i)
    (hj : h.val.val j = 0) (rj : r.val (hexIndexEquiv j) = 0) (k : HexIndex) :
    hammingNorm (fun a => c0Encoder (h.val,r) (k,a)) =
      if k = i then 4 else if k = j then 0 else 2 := by
  obtain ⟨j₀,hj₀,huniq⟩ := hexZeroCoordinate_unique_other_zero i h hh
  have he : j₀ = j := (huniq j ⟨hji,hj⟩).symm
  subst j₀
  change hammingNorm (Atlas.Codes.j (h.val.val k) + fun _ => r.val (hexIndexEquiv k)) = _
  rw [complemented_j_weight]
  by_cases hki : k = i
  · subst k
    have hi : h.val.val i = 0 := h.prop
    simp [hi,ri]
  by_cases hkj : k = j
  · subst k
    simp [hj,rj,hji]
  have hk : h.val.val k ≠ 0 := fun hz => hkj (huniq k ⟨hki,hz⟩)
  simp [hk,hki,hkj]

end Atlas.Codes
