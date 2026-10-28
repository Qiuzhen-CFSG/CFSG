/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.TetradCodeMinimum
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# TetradCodeGluing

The even subcode of a tetrad code is reconstructed from its decoded hexacode and a
gluing parity functional. The remainder parity vanishes on the decoding kernel, so it
descends to the recovered code and characterizes membership.

Source: `Atlas/Codes/TetradCodeGluing.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open scoped BigOperators

def tetradGluingParity (E : Submodule Bit BinaryWord) : tetradEvenSubcode E →ₗ[Bit] Bit where
  toFun w := ∑ i, tetradRemainder E w i
  map_add' := by intros; simp [Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.mul_sum]

theorem tetradGluingParity_kernel (E : Submodule Bit BinaryWord) (hE : IsTetradCode E) :
    (tetradDecode E).ker ≤ (tetradGluingParity E).ker := by
  rw [tetradDecode_kernel E hE]
  rintro _ ⟨r,rfl⟩
  change ∑ i, rho r.val (hexPos i,0) = 0
  simpa [rho] using (parityCode_mem 5 r.val).mp r.prop

/-- The gluing functional descends through the precisely computed repetition kernel. -/
def tetradGluing (E : Submodule Bit BinaryWord) (hE : IsTetradCode E) :
    tetradHexacode E →ₗ[Bit] Bit :=
  ((tetradDecode E).ker.liftQ (tetradGluingParity E) (tetradGluingParity_kernel E hE)).comp
    (tetradQuotientEquiv E).symm.toLinearMap

theorem tetradGluing_apply (E : Submodule Bit BinaryWord) (hE : IsTetradCode E)
    (w : tetradEvenSubcode E) :
    tetradGluing E hE ⟨tetradDecode E w,⟨w,rfl⟩⟩ = ∑ i, tetradRemainder E w i := by
  have he := (tetradDecode E).quotKerEquivRange_symm_apply_image w
    (show tetradDecode E w ∈ (tetradDecode E).range from ⟨w,rfl⟩)
  exact congrArg ((tetradDecode E).ker.liftQ (tetradGluingParity E)
    (tetradGluingParity_kernel E hE)) he

theorem tetradGluing_mem_iff (E : Submodule Bit BinaryWord) (hE : IsTetradCode E)
    (h : tetradHexacode E) (r : Fin 6 → Bit) :
    jWord h.val + rho r ∈ E ↔ ∑ i, r i = tetradGluing E hE h := by
  constructor
  · intro he
    let w : tetradEvenSubcode E := ⟨⟨jWord h.val + rho r,he⟩,by
      change blockParity (jWord h.val + rho r) (0,0) = 0
      simp [blockParity,jWord,rho,Finset.sum_add_distrib]⟩
    have hd : tetradDecode E w = h.val := by
      funext i
      change blockDecode (j (h.val i) + fun _ => r (hexIndexEquiv i)) = _
      simp
    have hr : tetradRemainder E w = r := by
      funext i
      simp [tetradRemainder,w,jWord,rho]
    have hh : (⟨tetradDecode E w,⟨w,rfl⟩⟩ : tetradHexacode E) = h := Subtype.ext hd
    rw [← hh,tetradGluing_apply,hr]
  · intro hr
    obtain ⟨h,⟨w,rfl⟩⟩ := h
    rw [tetradGluing_apply] at hr
    exact tetradEven_change_constants E hE w r hr

theorem tetradGluing_represented (E : Submodule Bit BinaryWord) (hE : IsTetradCode E) :
    ∃ t : HexWord, ∀ h : tetradHexacode E, tetradGluing E hE h = wordPolar h.val t := by
  obtain ⟨f,hf⟩ := (tetradGluing E hE).exists_extend
  refine ⟨(wordPolar.toDual wordPolar_nondegenerate).symm f,?_⟩
  intro h
  rw [wordPolar_symmetric,LinearMap.BilinForm.apply_toDual_symm_apply]
  exact (DFunLike.congr_fun hf h).symm

end Atlas.Codes
