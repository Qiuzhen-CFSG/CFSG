/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeCounting

/-!
Binary parity codes with explicit encoders and bases.
Recovering the free coordinates proves the dimension and cardinality formulas.

Source: `Atlas/Codes/Parity.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0: public module imports and exposed definition bodies
preserve downstream coordinate reductions; proof syntax and simplifier arguments
are adjusted for this toolchain. The mathematical declarations are unchanged.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators

def parityEncoder (n : ℕ) : (Fin n → Bit) →ₗ[Bit] (Fin (n + 1) → Bit) where
  toFun r := Fin.cons (∑ i, r i) r
  map_add' := by
    intro r s
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Finset.sum_add_distrib]
    · simp
  map_smul' := by
    intro a r
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Finset.mul_sum]
    · simp

def parityCode (n : ℕ) : Submodule Bit (Fin (n + 1) → Bit) := (parityEncoder n).range

theorem parityEncoder_injective (n : ℕ) : Function.Injective (parityEncoder n) := by
  intro r s h
  funext i
  exact congrFun h i.succ

noncomputable def parityEquiv (n : ℕ) : (Fin n → Bit) ≃ₗ[Bit] parityCode n :=
  LinearEquiv.ofInjective (parityEncoder n) (parityEncoder_injective n)

theorem parityCode_mem (n : ℕ) (r : Fin (n + 1) → Bit) :
    r ∈ parityCode n ↔ ∑ i, r i = 0 := by
  constructor
  · rintro ⟨s, rfl⟩
    simp [parityEncoder, Fin.sum_univ_succ]
  · intro hr
    refine ⟨fun i => r i.succ, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change ∑ j : Fin n, r j.succ = r 0
      have hh := congrArg (fun x : Bit => r 0 + x) hr
      simpa [Fin.sum_univ_succ, ← add_assoc] using hh
    · rfl

theorem parityCode_finrank (n : ℕ) : Module.finrank Bit (parityCode n) = n := by
  rw [← (parityEquiv n).finrank_eq]
  simp

theorem parityCode_card (n : ℕ) : Nat.card (parityCode n) = 2 ^ n := by
  rw [← Nat.card_congr (parityEquiv n).toEquiv]
  simp [Nat.card_eq_fintype_card, ZMod.card]

noncomputable def parityBasis (n : ℕ) : Module.Basis (Fin n) Bit (parityCode n) :=
  (Pi.basisFun Bit (Fin n)).map (parityEquiv n)

theorem parityBasis_coe (n : ℕ) (i : Fin n) :
    (parityBasis n i : Fin (n + 1) → Bit) = Pi.single 0 1 + Pi.single i.succ 1 := by
  change parityEncoder n ((Pi.basisFun Bit (Fin n)) i) = _
  rw [Pi.basisFun_apply]
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [parityEncoder]
  · simp [parityEncoder, Pi.single_apply]

abbrev P6 := parityCode 5
end Atlas.Codes
