module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Census
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Matrix.Mul

/-!
# Coordinates for the cubic block action

Write a block vector as a first column `a ∈ F₂²` followed by a matrix
`C ∈ M₂(F₂)`. The transformations are
`(a,C) ↦ (l a, l C rᵀ + (l a)tᵀ)`, for `l,r ∈ SL₂(2)` and `t ∈ F₂²`.
The zero first column is the distinguished subgroup `V`.

`BlockCoordinates` requires an actual multiplicative equivalence and equality
of this transformation family with the ambient conjugation action. It does
not assert that the source configuration has these coordinates. `TensorCensus`
is the independent finite calculation still required for the model. Keeping
these obligations separate permits their proofs to proceed independently;
neither record by itself proves source 15.3.61.

Source: Aschbacher–Smith, 15.3.54(4), with `s=1`, and 15.3.61(2),
printed pp.1146,1150–1151.
-/

@[expose] public section
open Subgroup Matrix
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks

abbrev BinaryPlane := Fin 2 → ZMod 2
abbrev BinaryMatrix := Matrix (Fin 2) (Fin 2) (ZMod 2)
abbrev Frame := {m : BinaryMatrix // m.det = 1}
abbrev BlockModel := Multiplicative (Fin 2 → Fin 3 → ZMod 2)

def first (x : BlockModel) : BinaryPlane := fun i => Multiplicative.toAdd x i 0
def matrix (x : BlockModel) : BinaryMatrix :=
  fun i j => Multiplicative.toAdd x i j.succ

/-- The four-dimensional tensor subgroup, with zero first column. -/
def modelV : Subgroup BlockModel where
  carrier := {x | first x = 0}
  one_mem' := rfl
  mul_mem' := by
    intro x y hx hy
    change first x + first y = 0
    rw [hx, hy, zero_add]
  inv_mem' := by
    intro x hx
    change -first x = 0
    rw [hx, neg_zero]

/-- All transformations induced by the two linear factors and the inner
translations. This formula retains the distinguished tensor subgroup. -/
def transform (l r : Frame) (t : BinaryPlane) (x : BlockModel) : BlockModel :=
  Multiplicative.ofAdd fun i => Fin.cons
    ((l.val *ᵥ first x) i)
    (fun j => (l.val * matrix x * r.val.transpose) i j +
      (l.val *ᵥ first x) i * t j)

/-- Orbit relation for the explicitly specified transformations. -/
def Related (x y : BlockModel) : Prop :=
  ∃ l r : Frame, ∃ t : BinaryPlane, transform l r t x = y

def Singular (x : BlockModel) : Prop := x ∈ modelV ∧ x ≠ 1 ∧ (matrix x).det = 0
def Nonsingular (x : BlockModel) : Prop := x ∈ modelV ∧ (matrix x).det ≠ 0

/-- Representative of the orbit with twelve elements. -/
def outsideOne : BlockModel := Multiplicative.ofAdd ![![1, 0, 0], ![0, 0, 0]]
/-- Representative of the orbit with thirty-six elements. -/
def outsideTwo : BlockModel := Multiplicative.ofAdd ![![1, 0, 0], ![0, 1, 0]]

theorem outsideOne_not_mem : outsideOne ∉ modelV := by
  change first outsideOne ≠ 0
  decide
theorem outsideTwo_not_mem : outsideTwo ∉ modelV := by
  change first outsideTwo ≠ 0
  decide

/-- Literal six-coordinate equivalence, independent of any order argument. -/
def modelSixEquiv : BlockModel ≃* Multiplicative (Fin 6 → ZMod 2) where
  toFun x := Multiplicative.ofAdd fun k =>
    Multiplicative.toAdd x ((finProdFinEquiv (m := 2) (n := 3)).symm k).1
      ((finProdFinEquiv (m := 2) (n := 3)).symm k).2
  invFun x := Multiplicative.ofAdd fun i j =>
    Multiplicative.toAdd x (finProdFinEquiv (i, j))
  left_inv x := by
    funext i j
    simp
  right_inv x := by
    funext k
    simp
  map_mul' x y := rfl

variable {G : Type*} [Group G]

/-- Equality of the actual ambient action with the tensor transformation
family, not merely an abstract isomorphism of groups of the same order. -/
structure BlockCoordinates (I P V D : Subgroup G) where
  equiv : fusionBlock P V D ≃* BlockModel
  distinguished : ∀ x : fusionBlock P V D, (x : G) ∈ V ↔ equiv x ∈ modelV
  forward : ∀ g ∈ I, ∃ l r : Frame, ∃ t : BinaryPlane,
    ∀ x : fusionBlock P V D,
      MulAut.conj g (x : G) = (equiv.symm (transform l r t (equiv x)) : G)
  realize : ∀ l r : Frame, ∀ t : BinaryPlane, ∃ g ∈ I,
    ∀ x : fusionBlock P V D,
      MulAut.conj g (x : G) = (equiv.symm (transform l r t (equiv x)) : G)

/-- The intrinsic finite calculation. Its fields concern only the explicit
matrix transformations above; the ambient application must supply coordinates. -/
structure TensorCensus : Prop where
  singular_card : ∀ z, Singular z → Nat.card {x // Related z x} = 9
  nonsingular_card : ∀ v, Nonsingular v → Nat.card {x // Related v x} = 6
  outsideOne_card : Nat.card {x // Related outsideOne x} = 12
  outsideTwo_card : Nat.card {x // Related outsideTwo x} = 36
  singular_span : ∀ z, Singular z → closure {x | Related z x} = modelV
  nonsingular_span : ∀ v, Nonsingular v → closure {x | Related v x} = modelV
  cover : ∀ z, Singular z → ∀ v, Nonsingular v → ∀ x : BlockModel, x ≠ 1 →
    Related z x ∨ Related v x ∨ Related outsideOne x ∨ Related outsideTwo x

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks
