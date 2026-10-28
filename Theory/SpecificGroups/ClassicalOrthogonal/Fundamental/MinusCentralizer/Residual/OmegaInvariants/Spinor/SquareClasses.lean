/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.LinearCombination

/-!
# Square classes for the orthogonal spinor invariant

The quotient of the field units by their squares has two elements over a
finite field of odd characteristic. These definitions are shared by the
intrinsic spinor construction and its concrete minus-space calculations.

Adapted from `Atlas/Algebra/{SquareOneUnits,SquareClasses}.lean` and the
sign-counting part of `Atlas/LinearAlgebra/QuadraticScalar.lean`. We omit the
unneeded scalar isometries, add the field `IsSquare` interface, and expose
definitions through Lean 4.33 public module boundaries.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open scoped Classical
namespace Atlas
variable (F : Type*) [Field F]

def squareUnits : Subgroup Fˣ := (powMonoidHom 2 : Fˣ →* Fˣ).range
abbrev SquareClass := Fˣ ⧸ squareUnits F

def squareClass : Fˣ →* SquareClass F := QuotientGroup.mk' (squareUnits F)

theorem squareClass_eq_one (a : Fˣ) : squareClass F a = 1 ↔ ∃ b : Fˣ, b ^ 2 = a := by
  change (a : Fˣ ⧸ squareUnits F) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  rfl

@[simp] theorem squareClass_square (a : Fˣ) : squareClass F (a ^ 2) = 1 :=
  (squareClass_eq_one F _).mpr ⟨a, rfl⟩

theorem squareClass_mul_square (a b : Fˣ) : squareClass F (a * b ^ 2) = squareClass F a := by
  rw [map_mul, squareClass_square]
  exact mul_one (squareClass F a)

theorem squareClass_surjective : Function.Surjective (squareClass F) :=
  QuotientGroup.mk'_surjective _

theorem squareClass_mk0_eq_one (a : F) (ha : a ≠ 0) :
    squareClass F (Units.mk0 a ha) = 1 ↔ IsSquare a := by
  rw [squareClass_eq_one]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b.val, ?_⟩
    simpa only [Units.val_pow_eq_pow_val, Units.val_mk0, pow_two, Units.val_mul] using
      (congrArg Units.val hb).symm
  · rintro ⟨b, hb⟩
    have hb0 : b ≠ 0 := by intro h; simp [h] at hb; exact ha hb
    refine ⟨Units.mk0 b hb0, Units.ext ?_⟩
    simpa only [Units.val_pow_eq_pow_val, Units.val_mk0, pow_two, Units.val_mul] using hb.symm

private def squareOneUnitsEquiv : rootsOfUnity 2 F ≃ {a : F // a ^ 2 = 1} where
  toFun a := ⟨a.val.val, congrArg Units.val ((mem_rootsOfUnity 2 a.val).mp a.prop)⟩
  invFun a := ⟨Units.mk0 a.val (by
    intro h
    have ha := a.prop
    rw [h, zero_pow (by decide : 2 ≠ 0)] at ha
    exact zero_ne_one ha), by
      apply (mem_rootsOfUnity 2 _).mpr
      exact Units.ext a.prop⟩
  left_inv a := by apply Subtype.ext; apply Units.ext; rfl
  right_inv a := rfl

private def squareOneEquivSigns :
    {a : F // a ^ 2 = 1} ≃ (↑({1, -1} : Finset F) : Type _) where
  toFun a := ⟨a.val, by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using sq_eq_one_iff.mp a.prop⟩
  invFun a := ⟨a.val, sq_eq_one_iff.mpr (by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using a.prop)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_squareOneUnits : Nat.card (rootsOfUnity 2 F) = if (2 : F) = 0 then 1 else 2 := by
  classical
  rw [Nat.card_congr (squareOneUnitsEquiv F), Nat.card_congr (squareOneEquivSigns F),
    Nat.card_eq_fintype_card, Fintype.card_coe]
  by_cases h : (2 : F) = 0
  · have hsign : (1 : F) = -1 := by linear_combination h
    rw [Finset.card_insert_of_mem (Finset.mem_singleton.mpr hsign),
      Finset.card_singleton, if_pos h]
  · have hsign : (1 : F) ≠ -1 := by intro he; apply h; linear_combination he
    rw [if_neg h]
    exact Finset.card_pair_eq_two_iff.mpr hsign

theorem card_squareClass [Finite F] :
    Nat.card (SquareClass F) = if (2 : F) = 0 then 1 else 2 := by
  have hker : (powMonoidHom 2 : Fˣ →* Fˣ).ker = rootsOfUnity 2 F := by
    ext a
    exact (mem_rootsOfUnity 2 a).symm
  change (powMonoidHom 2 : Fˣ →* Fˣ).range.index = _
  rw [Subgroup.index_range, hker, card_squareOneUnits]

end Atlas
