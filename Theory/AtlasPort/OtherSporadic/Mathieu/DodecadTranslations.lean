/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.DodecadMaskImage
public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetRecovery
public import Theory.AtlasPort.OtherSporadic.Mathieu.TetradPointwiseStabilizer

/-!
# DodecadTranslations

Admissible dodecad masks with the same nonzero hexacode parameter are related by actual
tetrad-fixing translations. The polar mask image gives the translation, and the encoder
identity verifies its action on the word and support.

Source: `Atlas/Mathieu/DodecadTranslations.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open scoped BigOperators

theorem dodecad_translation_parameters (i : HexIndex) (h : hexZeroCoordinate i) (hh : h ≠ 0)
    (r s : P6) (hz : ∀ k, h.val.val k = 0 → r.val (hexIndexEquiv k) = s.val (hexIndexEquiv k)) :
    ∃ t : hexZeroCoordinate i, ∀ k : HexIndex,
      r.val (hexIndexEquiv k) + polar (h.val.val k) (t.val.val k) = s.val (hexIndexEquiv k) := by
  classical
  let d : HexIndex → Bit := fun k => s.val (hexIndexEquiv k) - r.val (hexIndexEquiv k)
  have hd0 (k : HexIndex) (hk : h.val.val k = 0) : d k = 0 := by simp [d,hz k hk]
  have hsum : (∑ k, d k) = 0 := by
    simp only [d, Finset.sum_sub_distrib, hexIndexEquiv.sum_comp,
      (parityCode_mem 5 _).mp r.prop, (parityCode_mem 5 _).mp s.prop, sub_self]
  have hm : (fun k : DodecadMaskPositions i h => d k) ∈ dodecadEvenMasks i h := by
    change (∑ k : DodecadMaskPositions i h, d k) = 0
    calc
      _ = ∑ k ∈ Finset.univ.filter (fun k => h.val.val k ≠ 0), d k := by
        symm
        apply Finset.sum_subtype
        intro k
        simp
      _ = ∑ k, d k := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : h.val.val k = 0 <;> simp [hk,hd0 k]
      _ = 0 := hsum
  rw [← dodecadMaskMap_range i h hh] at hm
  obtain ⟨t,ht⟩ := hm
  refine ⟨t,fun k => ?_⟩
  by_cases hk : h.val.val k = 0
  · simp [hk,hz k hk]
  · have he : polar (h.val.val k) (t.val.val k) = d k := congrFun ht ⟨k,hk⟩
    rw [he]
    dsimp [d]
    abel

theorem dodecad_translation_word (i : HexIndex) (h t : hexZeroCoordinate i) (r s : P6)
    (ht : ∀ k : HexIndex, r.val (hexIndexEquiv k) + polar (h.val.val k) (t.val.val k) =
      s.val (hexIndexEquiv k)) :
    coordinatePermutation (affinePermutation t.val.val 1) (c0Encoder (h.val,r)) =
      c0Encoder (h.val,s) := by
  have he := affine_encoder_transform t.val.val 1 h.val.val
    (fun k => r.val (hexIndexEquiv k)) 0
  rw [rowEncoder_C0] at he
  have hr : affineRepetition t.val.val 1 h.val.val (fun k => r.val (hexIndexEquiv k)) 0 =
      fun k => s.val (hexIndexEquiv k) := by
    funext k
    change r.val (hexIndexEquiv k) + polar (h.val.val k) (t.val.val k) + 0 * _ = _
    simpa only [zero_mul, add_zero] using ht k
  rw [hr] at he
  simp only [Monomial.act_one, zero_smul, add_zero, rowEncoder_C0] at he
  exact he

theorem dodecad_translation_actual (i : HexIndex) (h : hexZeroCoordinate i) (hh : h ≠ 0)
    (r s : P6) (hz : ∀ k, h.val.val k = 0 → r.val (hexIndexEquiv k) = s.val (hexIndexEquiv k)) :
    ∃ g : TetradPointStabilizer i,
      coordinatePermutation g.val.val (c0Encoder (h.val,r)) = c0Encoder (h.val,s) := by
  obtain ⟨t,ht⟩ := dodecad_translation_parameters i h hh r s hz
  refine ⟨tetradPointStabilizerEquiv i
    (SemidirectProduct.inl (Multiplicative.ofAdd t)),?_⟩
  change coordinatePermutation (affinePermutation t.val.val 1) _ = _
  exact dodecad_translation_word i h t r s ht

end Atlas.Codes
