/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.EvenBlockGeometry
public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeUniqueness

/-!
# Parity in codes with a sextet decomposition

A self-dual, doubly even code of minimum weight eight containing the
even tetrad repetitions has common tetrad parity. Orthogonality against pairs
of repetitions proves this constraint. The minimum excludes whole tetrads,
giving surjective parity and dimensions twelve and eleven for the full and
even subcodes.

Source: `Atlas/Codes/TetradCodeParity.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open scoped BigOperators

/-- Properties transported from the fixed Golay code after choosing sextet coordinates. -/
structure IsTetradCode (E : Submodule Bit BinaryWord) : Prop where
  self_dual : E = binaryDot.orthogonal E
  doubly_even : ∀ w ∈ E, 4 ∣ hammingNorm w
  minimum : ∀ w ∈ E, w ≠ 0 → 8 ≤ hammingNorm w
  repetitions : R0 ≤ E

def wholeTetrad (i : HexIndex) : BinaryWord := rho (Pi.single (hexIndexEquiv i) 1)

theorem wholeTetrad_weight (i : HexIndex) : hammingNorm (wholeTetrad i) = 4 := by
  rw [wholeTetrad,rho_weight]
  classical
  simp [hammingNorm_eq_sum, Pi.single_apply]

theorem wholeTetrad_ne_zero (i : HexIndex) : wholeTetrad i ≠ 0 := by
  intro h
  have hh := wholeTetrad_weight i
  rw [h] at hh
  simp at hh

theorem wholeTetrad_dot (i : HexIndex) (w : BinaryWord) :
    binaryDot (wholeTetrad i) w = blockParity w i := by
  classical
  rw [binaryDot_apply,Fintype.sum_prod_type]
  simp only [wholeTetrad,rho,LinearMap.coe_mk,AddHom.coe_mk]
  simp only [Pi.single_apply,Equiv.apply_eq_iff_eq,ite_mul,one_mul,zero_mul,Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  simp [blockParity]

theorem wholeTetrad_pair_mem (i j : HexIndex) : wholeTetrad i+wholeTetrad j ∈ R0 := by
  refine ⟨Pi.single (hexIndexEquiv i) 1+Pi.single (hexIndexEquiv j) 1,?_,by simp [wholeTetrad]⟩
  apply (parityCode_mem 5 _).mpr
  simp [Finset.sum_add_distrib]

theorem tetradCode_orthogonal (E : Submodule Bit BinaryWord) (hE : IsTetradCode E)
    (u v : E) : binaryDot u.val v.val = 0 := by
  have hv : v.val ∈ binaryDot.orthogonal E := by rw [← hE.self_dual]; exact v.prop
  exact hv u.val u.prop

theorem tetradCode_common_parity (E : Submodule Bit BinaryWord) (hE : IsTetradCode E)
    (w : E) (i j : HexIndex) : blockParity w.val i = blockParity w.val j := by
  have hp := hE.repetitions (wholeTetrad_pair_mem i j)
  have he := tetradCode_orthogonal E hE ⟨wholeTetrad i+wholeTetrad j,hp⟩ w
  change binaryDot (wholeTetrad i+wholeTetrad j) w.val = 0 at he
  rw [map_add,LinearMap.add_apply,wholeTetrad_dot,wholeTetrad_dot] at he
  have hz := congrArg (fun z : Bit => z+blockParity w.val j) he
  simpa [add_assoc] using hz

def tetradParity (E : Submodule Bit BinaryWord) : E →ₗ[Bit] Bit where
  toFun w := blockParity w.val (0,0)
  map_add' := by intros; simp [blockParity,Finset.sum_add_distrib]
  map_smul' := by intros; simp [blockParity,Finset.mul_sum]

theorem tetradCode_no_wholeTetrad (E : Submodule Bit BinaryWord) (hE : IsTetradCode E)
    (i : HexIndex) : wholeTetrad i ∉ E := by
  intro hi
  have hm := hE.minimum _ hi (wholeTetrad_ne_zero i)
  rw [wholeTetrad_weight] at hm
  omega

theorem tetradCode_repetition_mem (E : Submodule Bit BinaryWord) (hE : IsTetradCode E)
    (r : Fin 6 → Bit) : rho r ∈ E ↔ r ∈ P6 := by
  classical
  constructor
  · intro hr
    apply (parityCode_mem 5 r).mpr
    by_contra hn
    have hs : ∑ i, r i = 1 := (bit_cases (∑ i, r i)).resolve_left hn
    have hp : r + Pi.single (hexIndexEquiv (0,0)) 1 ∈ P6 := by
      apply (parityCode_mem 5 _).mpr
      simp [Finset.sum_add_distrib,hs]
    have he := E.add_mem hr (hE.repetitions (show rho (r + Pi.single (hexIndexEquiv (0,0)) 1) ∈ R0 from ⟨_,hp,rfl⟩))
    have hx : rho r + rho (r + Pi.single (hexIndexEquiv (0,0)) 1) = wholeTetrad (0,0) := by
      funext p
      simp [rho,wholeTetrad,← add_assoc]
    rw [hx] at he
    exact tetradCode_no_wholeTetrad E hE (0,0) he
  · intro hr
    exact hE.repetitions ⟨r,hr,rfl⟩

theorem tetradParity_surjective (E : Submodule Bit BinaryWord) (hE : IsTetradCode E) :
    Function.Surjective (tetradParity E) := by
  have hn : ∃ w : E, tetradParity E w ≠ 0 := by
    by_contra h
    push Not at h
    have hd : wholeTetrad (0,0) ∈ binaryDot.orthogonal E := by
      intro w hw
      rw [binaryDot_symmetric, wholeTetrad_dot]
      exact h ⟨w,hw⟩
    rw [← hE.self_dual] at hd
    exact tetradCode_no_wholeTetrad E hE (0,0) hd
  obtain ⟨w,hw⟩ := hn
  intro b
  rcases bit_cases b with rfl | rfl
  · exact ⟨0,map_zero _⟩
  · exact ⟨w,by rcases bit_cases (tetradParity E w) with h | h; exact False.elim (hw h); exact h⟩

def tetradEvenSubcode (E : Submodule Bit BinaryWord) : Submodule Bit E := (tetradParity E).ker

theorem tetradEvenSubcode_mem (E : Submodule Bit BinaryWord) (hE : IsTetradCode E) (w : E) :
    w ∈ tetradEvenSubcode E ↔ ∀ i, blockParity w.val i = 0 := by
  constructor
  · intro hw i
    exact (tetradCode_common_parity E hE w i (0,0)).trans hw
  · intro hw; exact hw (0,0)

theorem tetradCode_finrank (E : Submodule Bit BinaryWord) (hE : IsTetradCode E) :
    Module.finrank Bit E = 12 := by
  have hd := binaryDot.finrank_orthogonal binaryDot_nondegenerate E
  have ha : Module.finrank Bit BinaryWord = 24 := by simp [BinaryWord,Omega,HexIndex]
  rw [← hE.self_dual,ha] at hd
  have hd' : Module.finrank Bit E = 24 - Module.finrank Bit E := hd
  omega

theorem tetradEvenSubcode_finrank (E : Submodule Bit BinaryWord) (hE : IsTetradCode E) :
    Module.finrank Bit (tetradEvenSubcode E) = 11 := by
  have hr : (tetradParity E).range = ⊤ := LinearMap.range_eq_top.mpr (tetradParity_surjective E hE)
  have hrank : Module.finrank Bit (tetradParity E).range = 1 := by
    rw [hr,finrank_top]
    exact Module.finrank_self Bit
  have hd : Module.finrank Bit (tetradParity E).range +
      Module.finrank Bit (tetradEvenSubcode E) = Module.finrank Bit E :=
    (tetradParity E).finrank_range_add_finrank_ker
  rw [hrank,tetradCode_finrank E hE] at hd
  omega

end Atlas.Codes
