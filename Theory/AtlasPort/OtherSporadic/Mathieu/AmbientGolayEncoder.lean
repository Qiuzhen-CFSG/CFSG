/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.AffineRows

/-!
# AmbientGolayEncoder

Block parity and block decoding recover all parameters of the ambient row encoder. This
proves injectivity and characterizes membership in Golay by the hexacode and even-mask
constraints.

Source: `Atlas/Mathieu/AmbientGolayEncoder.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators

/-- Four-row parity detects the quadratic coefficient, independently of code membership. -/
theorem affine_block_parity : ∀ (u : K) (r ε d : Bit),
    (∑ k : Fin 4, (polar u (rowLabel k) + r + ε * (1+qK (rowLabel k)+d))) = ε := by decide

theorem rowEncoder_blockParity (h : HexWord) (r : HexIndex → Bit) (ε : Bit) (i : HexIndex) :
    blockParity (rowEncoder h r ε) i = ε := affine_block_parity (h i) (r i) ε (lastColumnBit i)

theorem affine_linear_block_decode : ∀ (u : K) (r : Bit),
    blockDecode (fun k => polar u (rowLabel k)+r) = u := by decide

theorem rowEncoder_decode (h : HexWord) (r : HexIndex → Bit) (ε : Bit) :
    golayRawDecoder (rowEncoder h r ε) = (h,fun j => r (hexPos j),ε) := by
  simp only [golayRawDecoder,rowEncoder_blockParity]
  have he : rowEncoder h r ε - ε • eta = fun p => polar (h p.1) (rowLabel p.2) + r p.1 := by
    funext p
    change (polar (h p.1) (rowLabel p.2) + r p.1 +
      ε*(1+qK (rowLabel p.2)+lastColumnBit p.1)) - ε*eta p = _
    rw [eta_row_quadratic]
    exact add_sub_cancel_right _ _
  rw [he]
  apply Prod.ext
  · funext i; exact affine_linear_block_decode (h i) (r i)
  · apply Prod.ext
    · funext i
      have hz : rowLabel 0 = 0 := rfl
      simp only [hz,map_zero,zero_add]
      rfl
    · rfl

theorem rowEncoder_injective : Function.Injective
    (fun x : HexWord × (HexIndex → Bit) × Bit => rowEncoder x.1 x.2.1 x.2.2) := by
  rintro ⟨h,r,ε⟩ ⟨k,s,δ⟩ he
  have hd := congrArg golayRawDecoder he
  rw [rowEncoder_decode,rowEncoder_decode] at hd
  obtain ⟨hh,hrs⟩ := Prod.mk.inj hd
  obtain ⟨hr,hε⟩ := Prod.mk.inj hrs
  refine Prod.ext hh (Prod.ext ?_ hε)
  funext i
  simpa only [hexPos_index] using congrFun hr (hexIndexEquiv i)

theorem rowEncoder_mem_iff (h : HexWord) (r : HexIndex → Bit) (ε : Bit) :
    rowEncoder h r ε ∈ golay ↔ h ∈ hexacode ∧ ∑ i, r i = 0 := by
  constructor
  · intro hw
    obtain ⟨⟨k,s,δ⟩,he⟩ := golayEquiv.surjective ⟨rowEncoder h r ε,hw⟩
    have he' : rowEncoder k.val (fun i => s.val (hexIndexEquiv i)) δ = rowEncoder h r ε :=
      (rowEncoder_golayEquiv k s δ).trans (congrArg Subtype.val he)
    have hd := @rowEncoder_injective (k.val,(fun i => s.val (hexIndexEquiv i)),δ) (h,r,ε) he'
    have hh := (Prod.mk.inj hd).1
    have hr := (Prod.mk.inj (Prod.mk.inj hd).2).1
    refine ⟨hh ▸ k.prop,?_⟩
    rw [← hr,Equiv.sum_comp hexIndexEquiv]
    exact (parityCode_mem 5 s.val).mp s.prop
  · rintro ⟨hh,hr⟩
    let s : Fin 6 → Bit := fun j => r (hexPos j)
    have hs : s ∈ P6 := (parityCode_mem 5 s).mpr (by
      change (∑ j, r (hexIndexEquiv.symm j)) = 0
      rw [Equiv.sum_comp hexIndexEquiv.symm]; exact hr)
    have he := rowEncoder_golayEquiv ⟨h,hh⟩ ⟨s,hs⟩ ε
    have hr' : (fun i => s (hexIndexEquiv i)) = r := by
      funext i; exact congrArg r (hexPos_index i)
    rw [hr'] at he
    rw [he]
    exact (golayEquiv (⟨h,hh⟩,⟨s,hs⟩,ε)).prop

end Atlas.Codes
