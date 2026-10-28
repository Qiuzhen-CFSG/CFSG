/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetSplitExtension

/-!
# SextetRecovery

The sextet stabilizer preserves the even Golay subcode and acts equivariantly on its
recovered hexacode. The affine encoder formula identifies the quotient action, shows
translations act trivially there, and preserves the repetition kernel.

Source: `Atlas/Mathieu/SextetRecovery.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open scoped BigOperators

theorem rowEncoder_C0 (h : hexacode) (r : P6) :
    rowEncoder h.val (fun i => r.val (hexIndexEquiv i)) 0 = (c0Equiv (h,r) : BinaryWord) := by
  have he := rowEncoder_lift h.val r.val 0
  simp only [zero_smul,add_zero] at he
  exact he

theorem rowEncoder_zero_mem_C0 (h : HexWord) (r : HexIndex → Bit)
    (hh : h ∈ hexacode) (hr : ∑ i, r i = 0) : rowEncoder h r 0 ∈ C0 := by
  apply (C0_even_blocks _).mpr
  refine ⟨(rowEncoder_mem_iff _ _ _).mpr ⟨hh,hr⟩,?_⟩
  intro i
  apply (even_weight_iff _).mpr
  exact rowEncoder_blockParity h r 0 i

theorem recoverHex_rowEncoder (h : HexWord) (r : HexIndex → Bit)
    (hw : rowEncoder h r 0 ∈ C0) : (recoverHex ⟨rowEncoder h r 0,hw⟩).val = h := by
  funext i
  rw [recoverHex_blocks]
  have he : (fun k => rowEncoder h r 0 (i,k)) = fun k => polar (h i) (rowLabel k)+r i := by
    funext k; simp only [rowEncoder,zero_mul,add_zero]
  rw [he]
  exact affine_linear_block_decode (h i) (r i)

theorem affine_preserves_C0 (t : hexacode) (g : HexAutomorphisms) (w : C0) :
    coordinatePermutation (affinePermutation t.val g.val) w.val ∈ C0 := by
  obtain ⟨⟨h,r⟩,he⟩ := c0Equiv.surjective w
  have hrw := (rowEncoder_C0 h r).trans (congrArg Subtype.val he)
  rw [← hrw,affine_encoder_transform]
  have hh : Monomial.act g.val h.val ∈ hexacode := (g.prop _).mp h.prop
  apply rowEncoder_zero_mem_C0
  · simpa using hh
  · rw [affineRepetition_sum,Equiv.sum_comp hexIndexEquiv,
      (parityCode_mem 5 r.val).mp r.prop,hexacode_orthogonal _ _ hh t.prop]
    simp

theorem sextet_preserves_C0 (s : SextetStabilizer) (w : C0) :
    coordinatePermutation s.val.val w.val ∈ C0 := by
  obtain ⟨x,rfl⟩ := sextetAffineEquiv.surjective s
  exact affine_preserves_C0 x.left.toAdd x.right w

def sextetC0Action (s : SextetStabilizer) : C0 ≃ₗ[Bit] C0 where
  toFun w := ⟨coordinatePermutation s.val.val w.val,sextet_preserves_C0 s w⟩
  invFun w := ⟨coordinatePermutation s.val.val⁻¹ w.val,sextet_preserves_C0 s⁻¹ w⟩
  left_inv := by intro w; apply Subtype.ext; simp [← coordinatePermutation_mul]
  right_inv := by intro w; apply Subtype.ext; simp [← coordinatePermutation_mul]
  map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
  map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _

theorem recoverHex_equivariant (s : SextetStabilizer) (w : C0) :
    recoverHex (sextetC0Action s w) = hexAction (sextetQuotient s) (recoverHex w) := by
  obtain ⟨x,rfl⟩ := sextetAffineEquiv.surjective s
  obtain ⟨⟨h,r⟩,rfl⟩ := c0Equiv.surjective w
  rw [sextetQuotient_affine,recoverHex_apply]
  apply Subtype.ext
  funext i
  rw [recoverHex_blocks]
  have he := affine_encoder_transform x.left.toAdd.val x.right.val h.val
    (fun i => r.val (hexIndexEquiv i)) 0
  rw [rowEncoder_C0] at he
  have hb : (fun k => (sextetC0Action (sextetAffineEquiv x) (c0Equiv (h,r))).val (i,k)) =
      fun k => polar (Monomial.act x.right.val h.val i) (rowLabel k) +
        affineRepetition x.left.toAdd.val x.right.val h.val (fun i => r.val (hexIndexEquiv i)) 0 i := by
    funext k
    have hh := congrFun he (i,k)
    simp only [rowEncoder,Pi.add_apply,zero_smul,Pi.zero_apply,add_zero,zero_mul] at hh
    exact hh
  rw [hb,affine_linear_block_decode]
  rfl

theorem sextet_preserves_R0 (s : SextetStabilizer) (w : C0) :
    (sextetC0Action s w).val ∈ R0 ↔ w.val ∈ R0 := by
  rw [← recoverHex_kernel, recoverHex_equivariant,LinearEquiv.map_eq_zero_iff,recoverHex_kernel]

theorem sextet_translation_trivial_recovery (t : Multiplicative hexacode) (w : C0) :
    recoverHex (sextetC0Action (sextetTranslation t) w) = recoverHex w := by
  rw [recoverHex_equivariant,sextetQuotient_translation,map_one]
  rfl

theorem sextet_coordinate_compatibility (s : SextetStabilizer) (i : HexIndex) (k : Fin 4) :
    (s.val.val (i,k)).1 = hexCoordinateHom (sextetQuotient s) i := by
  obtain ⟨x,rfl⟩ := sextetAffineEquiv.surjective s
  rw [sextetQuotient_affine]
  rfl

end Atlas.Codes
