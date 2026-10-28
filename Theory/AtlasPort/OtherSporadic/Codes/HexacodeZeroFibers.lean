/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.HexacodeZeroCoordinate
public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeUniqueness

/-!
# HexacodeZeroFibers

Words vanishing at two distinct hexacode coordinates form a four-element space, linearly
equivalent to the alphabet by projection at a third coordinate. Three-coordinate
bijectivity also shows that a nonzero word vanishing once has exactly one other zero.

Source: `Atlas/Codes/HexacodeZeroFibers.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

def distinctHexTriple (i j k : HexIndex) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Fin 3 ↪ HexIndex :=
  ⟨![i,j,k], by
    intro x y h
    fin_cases x <;> fin_cases y <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]⟩

def hexDoubleZero (i j : HexIndex) : Submodule Bit hexacode :=
  (hexCoordinate i).ker ⊓ (hexCoordinate j).ker

def hexDoubleZeroProjection (i j k : HexIndex) : hexDoubleZero i j →ₗ[Bit] K :=
  (hexCoordinate k).comp (hexDoubleZero i j).subtype

theorem hexDoubleZeroProjection_bijective (i j k : HexIndex)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Function.Bijective (hexDoubleZeroProjection i j k) := by
  let e := distinctHexTriple i j k hij hik hjk
  constructor
  · intro u v h
    apply Subtype.ext
    apply hexProjection_injective e
    funext x
    fin_cases x
    · exact u.prop.1.trans v.prop.1.symm
    · exact u.prop.2.trans v.prop.2.symm
    · exact h
  · intro t
    obtain ⟨w,hw⟩ := (hexProjection_bijective e).2 ![0,0,t]
    exact ⟨⟨w,congrFun hw 0,congrFun hw 1⟩,congrFun hw 2⟩

def hexDoubleZeroEquiv (i j k : HexIndex) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    hexDoubleZero i j ≃ₗ[Bit] K :=
  LinearEquiv.ofBijective _ (hexDoubleZeroProjection_bijective i j k hij hik hjk)

theorem hexDoubleZero_card (i j : HexIndex) (hij : i ≠ j) : Nat.card (hexDoubleZero i j) = 4 := by
  have hx : ∀ i j : HexIndex, ∃ k, k ≠ i ∧ k ≠ j := by decide
  obtain ⟨k,hki,hkj⟩ := hx i j
  rw [Nat.card_congr (hexDoubleZeroEquiv i j k hij hki.symm hkj.symm).toEquiv]
  simp [K,Letter,Bit]

theorem hexDoubleZero_finrank (i j : HexIndex) (hij : i ≠ j) :
    Module.finrank Bit (hexDoubleZero i j) = 2 := by
  have hx : ∀ i j : HexIndex, ∃ k, k ≠ i ∧ k ≠ j := by decide
  obtain ⟨k,hki,hkj⟩ := hx i j
  rw [(hexDoubleZeroEquiv i j k hij hki.symm hkj.symm).finrank_eq]
  simp [K,Letter,Module.finrank_prod]

theorem hexZeroCoordinate_nonzero_weight (i : HexIndex) (h : hexZeroCoordinate i) (hh : h ≠ 0) :
    hammingNorm h.val.val = 4 := by
  have hn : h.val.val ≠ 0 := fun he => hh (Subtype.ext (Subtype.ext he))
  let e : Fin 1 ↪ HexIndex := ⟨fun _ => i,fun _ _ _ => Subsingleton.elim _ _⟩
  have hb := weight_le_of_zero_on_embedding e h.val.val (fun _ => h.prop)
  have hw := hex_weights h.val
  have hp := hammingNorm_pos_iff.mpr hn
  norm_num [HexIndex] at hb
  omega


theorem hexZeroCoordinate_unique_other_zero (i : HexIndex) (h : hexZeroCoordinate i) (hh : h ≠ 0) :
    ∃! j : HexIndex, j ≠ i ∧ h.val.val j = 0 := by
  classical
  have hw := hexZeroCoordinate_nonzero_weight i h hh
  obtain ⟨j,hji,hj⟩ : ∃ j : HexIndex, j ≠ i ∧ h.val.val j = 0 := by
    by_contra hn
    push Not at hn
    have hs : Finset.univ.filter (fun j => h.val.val j ≠ 0) = Finset.univ.erase i := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase]
      constructor
      · intro hz
        exact ⟨fun he => hz (he.symm ▸ h.prop),True.intro⟩
      · intro hj
        exact hn j hj.1
    have hc := congrArg Finset.card hs
    change hammingNorm h.val.val = _ at hc
    norm_num [HexIndex] at hc
    omega
  refine ⟨j,⟨hji,hj⟩,?_⟩
  intro k hk
  by_contra hkj
  have he := code_three_zeros hexacode hexacode_isHexMDS h.val i k j
    hk.1.symm hji.symm hkj h.prop hk.2 hj
  exact hh (Subtype.ext he)

end Atlas.Codes
