/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.GolayBasis

/-!
# GolayRecovery

Decoding even tetrads recovers the hexacode from the Golay even subcode, with the
repetition code as kernel. The analogous first-gluing map recovers the trio code;
explicit encoder inverses establish both surjections and kernels.

Source: `Atlas/Codes/GolayRecovery.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators

abbrev E4 := parityCode 3

theorem even_block_decomposition : ∀ w : Fin 4 → Bit, (∑ k, w k = 0) →
    w = j (blockDecode w) + fun _ => w 0 := by decide

theorem C0_even_blocks (w : BinaryWord) :
    w ∈ C0 ↔ w ∈ golay ∧ ∀ i, Even (hammingNorm (fun k => w (i,k))) := by
  constructor
  · rintro ⟨⟨h,r⟩,rfl⟩
    refine ⟨⟨(h,r,0),by simp [golayEncoder]⟩,?_⟩
    intro i
    rw [even_weight_iff]
    have hp := golayEncoder_blockParity h r 0 i
    simpa [golayEncoder, blockParity] using hp
  · rintro ⟨⟨⟨h,r,ε⟩,rfl⟩,hw⟩
    have hp := golayEncoder_blockParity h r ε (0,0)
    have hz := (even_weight_iff _).mp (hw (0,0))
    change blockParity (golayEncoder (h,r,ε)) (0,0) = 0 at hz
    rw [hp] at hz
    exact ⟨(h,r),by simp [golayEncoder,hz]⟩

noncomputable def recoverHex : C0 →ₗ[Bit] hexacode :=
  (LinearMap.fst Bit hexacode P6).comp c0Equiv.symm.toLinearMap

theorem recoverHex_apply (h : hexacode) (r : P6) : recoverHex (c0Equiv (h,r)) = h := by
  simp [recoverHex]

theorem recoverHex_blocks (w : C0) (i : HexIndex) :
    (recoverHex w).val i = blockDecode (fun k => w.val (i,k)) := by
  obtain ⟨⟨h,r⟩,rfl⟩ := c0Equiv.surjective w
  rw [recoverHex_apply]
  exact (c0Encoder_decode h r i).symm

theorem recoverHex_surjective : Function.Surjective recoverHex :=
  fun h => ⟨c0Equiv (h,0),recoverHex_apply h 0⟩

theorem recoverHex_kernel (w : C0) : recoverHex w = 0 ↔ w.val ∈ R0 := by
  constructor
  · intro hw
    obtain ⟨⟨h,r⟩,rfl⟩ := c0Equiv.surjective w
    rw [recoverHex_apply] at hw
    subst h
    refine ⟨r.val,r.prop,?_⟩
    have he : c0Encoder (0,r) = rho r.val := by simp [c0Encoder]
    exact he.symm
  · rintro ⟨r,hr,he⟩
    apply Subtype.ext
    funext i
    rw [recoverHex_blocks, ← he]
    change blockDecode (fun _ => r (hexIndexEquiv i)) = 0
    exact blockDecode_constant _

noncomputable def recoverTrio : H0 →ₗ[Bit] trio :=
  (LinearMap.fst Bit trio E0).comp firstGluing.symm.toLinearMap

theorem recoverTrio_apply (x : trio) (e : E0) : recoverTrio (firstGluing (x,e)) = x := by
  simp [recoverTrio]

theorem recoverTrio_surjective : Function.Surjective recoverTrio :=
  fun x => ⟨firstGluing (x,0),recoverTrio_apply x 0⟩

theorem recoverTrio_kernel (w : H0) : recoverTrio w = 0 ↔ w.val ∈ E0 := by
  constructor
  · intro hw
    obtain ⟨⟨x,e⟩,rfl⟩ := firstGluing.surjective w
    rw [recoverTrio_apply] at hw
    subst x
    rw [firstGluing_apply]
    simp
  · intro hw
    have he : w = firstGluing (0,⟨w.val,hw⟩) := by
      apply Subtype.ext
      rw [firstGluing_apply]
      simp
    rw [he,recoverTrio_apply]

end Atlas.Codes
