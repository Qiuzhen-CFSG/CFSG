/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.BinaryLift

/-!
The constructed binary Golay code has dimension twelve and 4096 words.
Block decoding proves the encoder injective and identifies its two disjoint
cosets over the eleven-dimensional even subcode.

Source: `Atlas/Codes/GolayConstruction.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0: public module imports and exposed definition bodies
preserve downstream coordinate reductions; proof syntax and simplifier arguments
are adjusted for this toolchain. The mathematical declarations are unchanged.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators

theorem c0Encoder_first (h : hexacode) (r : P6) (i : HexIndex) :
    c0Encoder (h, r) (i, 0) = r.val (hexIndexEquiv i) := by
  simp [c0Encoder, jWord, rho]

theorem c0Encoder_decode (h : hexacode) (r : P6) (i : HexIndex) :
    blockDecode (fun k => c0Encoder (h, r) (i, k)) = h.val i := by
  change blockDecode (j (h.val i) + fun _ => r.val (hexIndexEquiv i)) = _
  rw [map_add, blockDecode_j, blockDecode_constant, add_zero]

theorem c0Encoder_injective : Function.Injective c0Encoder := by
  rintro ⟨h, r⟩ ⟨h', r'⟩ he
  apply Prod.ext
  · apply Subtype.ext
    funext i
    simpa only [c0Encoder_decode] using congrArg (fun w : BinaryWord => blockDecode (fun k => w (i,k))) he
  · apply Subtype.ext
    funext i
    have h := congrArg (fun w : BinaryWord => w (hexIndexEquiv.symm i, 0)) he
    simpa only [c0Encoder_first, Equiv.apply_symm_apply] using h

theorem golayEncoder_injective : Function.Injective golayEncoder := by
  rintro ⟨h, r, ε⟩ ⟨h', r', ε'⟩ he
  have hε := congrArg (fun w : BinaryWord => blockParity w (0, 0)) he
  simp only [golayEncoder_blockParity] at hε
  have h0 : c0Encoder (h,r) = c0Encoder (h',r') := by
    change c0Encoder (h,r) + ε • eta = c0Encoder (h',r') + ε' • eta at he
    rw [hε] at he
    exact add_right_cancel he
  have hh := c0Encoder_injective h0
  exact Prod.ext (congrArg (fun x : hexacode × P6 => x.1) hh) (Prod.ext (congrArg (fun x : hexacode × P6 => x.2) hh) hε)

noncomputable def c0Equiv : (hexacode × P6) ≃ₗ[Bit] C0 :=
  LinearEquiv.ofInjective c0Encoder c0Encoder_injective
noncomputable def golayEquiv : (hexacode × P6 × Bit) ≃ₗ[Bit] golay :=
  LinearEquiv.ofInjective golayEncoder golayEncoder_injective

theorem golayEquiv_apply (h : hexacode) (r : P6) (ε : Bit) :
    (golayEquiv (h,r,ε) : BinaryWord) = jWord h.val + rho r.val + ε • eta := rfl

def golayRawDecoder (w : BinaryWord) : HexWord × (Fin 6 → Bit) × Bit :=
  let ε := blockParity w (0,0)
  let v := w - ε • eta
  (fun i => blockDecode (fun k => v (i,k)), fun i => v (hexIndexEquiv.symm i,0), ε)

theorem golay_decode_encode (h : hexacode) (r : P6) (ε : Bit) :
    golayRawDecoder (golayEncoder (h,r,ε)) = (h.val,r.val,ε) := by
  simp only [golayRawDecoder, golayEncoder_blockParity]
  have he : golayEncoder (h,r,ε) - ε • eta = c0Encoder (h,r) := by
    change c0Encoder (h,r) + ε • eta - ε • eta = _
    exact add_sub_cancel_right _ _
  simp only [he, c0Encoder_decode, c0Encoder_first, Equiv.apply_symm_apply]

theorem C0_finrank : Module.finrank Bit C0 = 11 := by
  rw [← c0Equiv.finrank_eq]
  simp [Module.finrank_prod, hexacode_finrank, P6, parityCode_finrank]

theorem golay_finrank : Module.finrank Bit golay = 12 := by
  rw [← golayEquiv.finrank_eq]
  simp [Module.finrank_prod, hexacode_finrank, P6, parityCode_finrank]

theorem golay_card : Nat.card golay = 4096 := by
  rw [← Nat.card_congr golayEquiv.toEquiv]
  rw [Nat.card_prod, Nat.card_prod, hexacode_card, parityCode_card]
  norm_num [Nat.card_eq_fintype_card, ZMod.card]

theorem C0_card : Nat.card C0 = 2048 := by
  rw [← Nat.card_congr c0Equiv.toEquiv]
  rw [Nat.card_prod, hexacode_card, parityCode_card]
  norm_num

theorem golay_cosets (w : BinaryWord) :
    w ∈ golay ↔ w ∈ C0 ∨ ∃ v ∈ C0, w = v + eta := by
  constructor
  · rintro ⟨⟨h,r,ε⟩, rfl⟩
    rcases bit_cases ε with he | he
    · left; exact ⟨(h,r), by simp [golayEncoder, he]⟩
    · right; exact ⟨c0Encoder (h,r), ⟨(h,r),rfl⟩, by simp [golayEncoder, he]⟩
  · rintro (⟨⟨h,r⟩,rfl⟩ | ⟨_,⟨⟨h,r⟩,rfl⟩,rfl⟩)
    · exact ⟨(h,r,0),by simp [golayEncoder]⟩
    · exact ⟨(h,r,1),by simp [golayEncoder]⟩

theorem eta_not_mem_C0 : eta ∉ C0 := by
  rintro ⟨⟨h,r⟩, he⟩
  have hh : golayEncoder (h,r,0) = golayEncoder (0,0,1) := by
    simpa [golayEncoder, c0Encoder] using he
  have hh' := congrArg (fun x : hexacode × P6 × Bit => x.2.2) (golayEncoder_injective hh)
  exact zero_ne_one hh'

theorem golay_cosets_disjoint (w : BinaryWord) (hw : w ∈ C0) :
    ¬ ∃ v ∈ C0, w = v + eta := by
  rintro ⟨v,hv,h⟩
  apply eta_not_mem_C0
  have hh := C0.sub_mem hw hv
  rwa [h, add_sub_cancel_left] at hh

end Atlas.Codes
