/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeSystematic

/-!
# HexacodeMDS

For a binary six-dimensional code of length six and minimum weight four, projection onto
any three Kleinian coordinates is bijective. The minimum proves injectivity and
dimensions give surjectivity, providing a systematic encoder with invertible local
coefficients.

Source: `Atlas/Codes/HexacodeMDS.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open scoped BigOperators

/-- The dimension and distance assumptions used by structural hexacode uniqueness. -/
structure IsHexMDS (D : Submodule Bit HexWord) : Prop where
  dimension : Module.finrank Bit D = 6
  minimum : ∀ w ∈ D, w ≠ 0 → 4 ≤ hammingNorm w

def codeTripleProjection (D : Submodule Bit HexWord) (e : Fin 3 ↪ HexIndex) :
    D →ₗ[Bit] (Fin 3 → K) where
  toFun w j := w.val (e j)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem codeTripleProjection_injective (D : Submodule Bit HexWord) (hD : IsHexMDS D)
    (e : Fin 3 ↪ HexIndex) : Function.Injective (codeTripleProjection D e) := by
  intro u v h
  have hz : ∀ j, (u.val-v.val) (e j) = 0 := fun j => sub_eq_zero.mpr (congrFun h j)
  have hb := weight_le_of_zero_on_embedding e (u.val-v.val) hz
  have hzero : u.val-v.val = 0 := by
    by_contra hn
    have hm := hD.minimum _ (D.sub_mem u.prop v.prop) hn
    norm_num [HexIndex] at hb
    omega
  exact Subtype.ext (sub_eq_zero.mp hzero)

theorem codeTripleProjection_bijective (D : Submodule Bit HexWord) (hD : IsHexMDS D)
    (e : Fin 3 ↪ HexIndex) : Function.Bijective (codeTripleProjection D e) := by
  have hd : Module.finrank Bit D = Module.finrank Bit (Fin 3 → K) := by
    rw [hD.dimension]
    rw [Module.finrank_pi_fintype, show Module.finrank Bit K = 2 by
      change Module.finrank Bit (Bit × Bit) = 2
      rw [Module.finrank_prod]
      norm_num]
    norm_num
  exact ⟨codeTripleProjection_injective D hD e,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp
      (codeTripleProjection_injective D hD e)⟩

theorem code_three_zeros (D : Submodule Bit HexWord) (hD : IsHexMDS D)
    (w : D) (i j k : HexIndex) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : w.val i = 0) (hj : w.val j = 0) (hk : w.val k = 0) : w = 0 := by
  let e : Fin 3 ↪ HexIndex := ⟨![i,j,k],by
    intro x y h
    fin_cases x <;> fin_cases y <;>
      simp_all [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]⟩
  apply codeTripleProjection_injective D hD e
  funext x
  fin_cases x <;> assumption

def lastThree : Fin 3 ↪ HexIndex where
  toFun i := hexPos (Fin.natAdd 3 i)
  inj' := by
    intro i j h
    apply Fin.ext
    have he := congrArg Fin.val (hexIndexEquiv.symm.injective h)
    change 3+i.val = 3+j.val at he
    omega

theorem firstThree_ne_lastThree (i j : Fin 3) : firstThree i ≠ lastThree j := by
  intro h
  have := congrArg Fin.val (hexIndexEquiv.symm.injective h)
  change i.val = 3+j.val at this
  omega

def mdsInputEquiv (D : Submodule Bit HexWord) (hD : IsHexMDS D) : D ≃ₗ[Bit] (Fin 3 → K) :=
  LinearEquiv.ofBijective (codeTripleProjection D firstThree) (codeTripleProjection_bijective D hD firstThree)

def mdsEncoder (D : Submodule Bit HexWord) (hD : IsHexMDS D) : (Fin 3 → K) →ₗ[Bit] HexWord :=
  D.subtype.comp (mdsInputEquiv D hD).symm.toLinearMap

@[simp] theorem mdsEncoder_first (D : Submodule Bit HexWord) (hD : IsHexMDS D)
    (x : Fin 3 → K) (i : Fin 3) : mdsEncoder D hD x (firstThree i) = x i :=
  congrFun ((mdsInputEquiv D hD).apply_symm_apply x) i

def mdsCoefficient (D : Submodule Bit HexWord) (hD : IsHexMDS D) (i j : Fin 3) : K →ₗ[Bit] K where
  toFun u := mdsEncoder D hD (Pi.single j u) (lastThree i)
  map_add' := by intros; simp [Pi.single_add, map_add]
  map_smul' := by intros; simp [Pi.single_smul, map_smul]

theorem mdsCoefficient_injective (D : Submodule Bit HexWord) (hD : IsHexMDS D)
    (i j : Fin 3) : Function.Injective (mdsCoefficient D hD i j) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro u hu
  have hex : ∀ j : Fin 3, ∃ k l : Fin 3, k ≠ j ∧ l ≠ j ∧ k ≠ l := by decide
  obtain ⟨k,l,hkj,hlj,hkl⟩ := hex j
  have hw := code_three_zeros D hD ((mdsInputEquiv D hD).symm (Pi.single j u))
    (firstThree k) (firstThree l) (lastThree i)
    (firstThree.injective.ne hkl) (firstThree_ne_lastThree k i) (firstThree_ne_lastThree l i)
    (by change mdsEncoder D hD _ _ = 0; simp [hkj])
    (by change mdsEncoder D hD _ _ = 0; simp [hlj]) hu
  have he := congrArg (fun w : D => w.val (firstThree j)) hw
  change mdsEncoder D hD (Pi.single j u) (firstThree j) = 0 at he
  simpa using he

def mdsCoefficientEquiv (D : Submodule Bit HexWord) (hD : IsHexMDS D) (i j : Fin 3) : KIsometry :=
  LinearEquiv.ofBijective (mdsCoefficient D hD i j)
    ⟨mdsCoefficient_injective D hD i j,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp (mdsCoefficient_injective D hD i j)⟩

theorem mdsEncoder_last (D : Submodule Bit HexWord) (hD : IsHexMDS D)
    (x : Fin 3 → K) (i : Fin 3) :
    mdsEncoder D hD x (lastThree i) = ∑ j, mdsCoefficientEquiv D hD i j (x j) := by
  have hx : x = ∑ j, Pi.single j (x j) := (Finset.univ_sum_single x).symm
  conv_lhs => rw [hx]
  simp only [map_sum,Finset.sum_apply]
  rfl

end Atlas.Codes
