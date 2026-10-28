/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.TetradCodeGluing

/-!
# TetradOddExtension

The odd part of a normalized tetrad code is forced by its even subcode. Decoding an odd
word and using orthogonality reduces the alternatives; the incorrect extension has
weight six and contradicts the minimum.

Source: `Atlas/Codes/TetradOddExtension.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open scoped BigOperators

def blockWordDecode (w : BinaryWord) : HexWord := fun i => blockDecode (fun k => w (i,k))
def blockWordConstants (w : BinaryWord) : Fin 6 → Bit := fun i => w (hexPos i,0)

theorem evenWord_decomposition (w : BinaryWord) (hw : ∀ i, blockParity w i = 0) :
    w = jWord (blockWordDecode w) + rho (blockWordConstants w) := by
  funext p
  obtain ⟨i,k⟩ := p
  simpa [jWord,rho,blockWordDecode,blockWordConstants] using
    congrFun (even_block_decomposition (fun k => w (i,k)) (hw i)) k

theorem binaryWord_add_self (w : BinaryWord) : w+w = 0 := by funext p; exact bit_self_add _

theorem oddWord_decode_mem (E : Submodule Bit BinaryWord) (hE : IsTetradCode E)
    (D : Submodule Bit HexWord) (hD : D = dual D)
    (hj : ∀ h ∈ D, jWord h ∈ E) (z : E) (hz : ∀ i, blockParity z.val i = 1) :
    blockWordDecode (z.val+eta) ∈ D := by
  rw [hD]
  intro h hh
  have hpar : ∀ i, blockParity (z.val+eta) i = 0 := by
    intro i
    simp [blockParity,Finset.sum_add_distrib,show ∑ k, z.val (i,k) = 1 from hz i]
  have he := evenWord_decomposition (z.val+eta) hpar
  have hzj := tetradCode_orthogonal E hE ⟨jWord h,hj h hh⟩ z
  have hd : binaryDot (jWord h) (z.val+eta) = 0 := by
    rw [map_add,hzj,binaryDot_symmetric (jWord h) eta,eta_jWord_dot,add_zero]
  rw [he,map_add,jWord_dot,jWord_rho_dot,add_zero] at hd
  exact hd

theorem eta_wrong_extension_weight : hammingNorm (eta + wholeTetrad (2,1)) = 6 := by decide

/-- Once the even gluing is zero, double evenness forces the unique odd extension. -/
theorem normalizedTetradCode_eta (E : Submodule Bit BinaryWord) (hE : IsTetradCode E)
    (D : Submodule Bit HexWord) (hD : D = dual D)
    (hj : ∀ h ∈ D, jWord h ∈ E) : eta ∈ E := by
  classical
  obtain ⟨z,hz⟩ := tetradParity_surjective E hE 1
  have hp : ∀ i, blockParity z.val i = 1 := fun i =>
    (tetradCode_common_parity E hE z i (0,0)).trans hz
  let h := blockWordDecode (z.val+eta)
  let r := blockWordConstants (z.val+eta)
  have hh : h ∈ D := oddWord_decode_mem E hE D hD hj z hp
  have hpar : ∀ i, blockParity (z.val+eta) i = 0 := by
    intro i
    simp [blockParity,Finset.sum_add_distrib,show ∑ k, z.val (i,k) = 1 from hp i]
  have he : z.val+eta = jWord h+rho r := evenWord_decomposition _ hpar
  rcases bit_cases (∑ i, r i) with hr | hr
  · have hd : jWord h + rho r ∈ E := E.add_mem (hj h hh)
      (hE.repetitions ⟨r,(parityCode_mem 5 r).mpr hr,rfl⟩)
    have ht := E.add_mem z.prop hd
    rw [← he,← add_assoc,binaryWord_add_self,zero_add] at ht
    exact ht
  · let s : Fin 6 → Bit := r+Pi.single (hexIndexEquiv (2,1)) 1
    have hs : s ∈ P6 := (parityCode_mem 5 s).mpr (by simp [s,Finset.sum_add_distrib,hr])
    have hd : jWord h + rho s ∈ E := E.add_mem (hj h hh) (hE.repetitions ⟨s,hs,rfl⟩)
    have ht := E.add_mem z.prop hd
    have hx : z.val + (jWord h+rho s) = eta+wholeTetrad (2,1) := by
      have he' : jWord h+rho s = z.val+eta+wholeTetrad (2,1) := by
        rw [show rho s = rho r+wholeTetrad (2,1) from map_add rho r _,← add_assoc,← he]
      rw [he',← add_assoc,← add_assoc,binaryWord_add_self,zero_add]
    rw [hx] at ht
    have hn := hE.doubly_even _ ht
    rw [eta_wrong_extension_weight] at hn
    norm_num at hn

theorem normalizedTetradCode_even_decode (E : Submodule Bit BinaryWord) (hE : IsTetradCode E)
    (D : Submodule Bit HexWord) (hD : D = dual D)
    (hj : ∀ h ∈ D, jWord h ∈ E) (w : E) (hw : ∀ i, blockParity w.val i = 0) :
    blockWordDecode w.val ∈ D := by
  rw [hD]
  intro h hh
  have he := tetradCode_orthogonal E hE ⟨jWord h,hj h hh⟩ w
  rw [evenWord_decomposition w.val hw,map_add,jWord_dot,jWord_rho_dot,add_zero] at he
  exact he

/-- Equality of the entire marked code, including both common-parity fibers. -/
theorem normalizedTetradCode_mem (E : Submodule Bit BinaryWord) (hE : IsTetradCode E)
    (D : Submodule Bit HexWord) (hD : D = dual D)
    (hj : ∀ h ∈ D, jWord h ∈ E) (w : BinaryWord) :
    w ∈ E ↔ ∃ (h : D) (r : P6) (ε : Bit), w = jWord h.val + rho r.val + ε • eta := by
  have hη := normalizedTetradCode_eta E hE D hD hj
  constructor
  · intro hw
    let ε := blockParity w (0,0)
    let v := w+ε • eta
    have hv : v ∈ E := E.add_mem hw (E.smul_mem ε hη)
    have hp : ∀ i, blockParity v i = 0 := by
      intro i
      have hc := tetradCode_common_parity E hE ⟨w,hw⟩ i (0,0)
      simp [v,blockParity,Finset.sum_add_distrib,← Finset.mul_sum,ε,← hc]
    let h := blockWordDecode v
    let r := blockWordConstants v
    have hh : h ∈ D := normalizedTetradCode_even_decode E hE D hD hj ⟨v,hv⟩ hp
    have he : v = jWord h + rho r := evenWord_decomposition v hp
    have hr : r ∈ P6 := by
      apply (tetradCode_repetition_mem E hE r).mp
      have ht := E.add_mem (hj h hh) hv
      rw [he,← add_assoc,binaryWord_add_self,zero_add] at ht
      exact ht
    refine ⟨⟨h,hh⟩,⟨r,hr⟩,ε,?_⟩
    rw [← he]
    change w = (w+ε • eta)+ε • eta
    rw [add_assoc,binaryWord_add_self,add_zero]
  · rintro ⟨h,r,ε,rfl⟩
    exact E.add_mem (E.add_mem (hj h.val h.prop) (hE.repetitions ⟨r.val,r.prop,rfl⟩))
      (E.smul_mem ε hη)

end Atlas.Codes
