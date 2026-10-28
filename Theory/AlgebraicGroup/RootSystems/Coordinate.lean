module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Real.Basic

namespace Theory.AlgebraicGroup.StandardRootSystem

public abbrev Vec (n : ℕ) := Fin n → ℝ

@[expose]
public noncomputable def halfSignVector {n : ℕ} (ε : Fin n → Bool) : Vec n :=
  fun i => if ε i then (1 / 2 : ℝ) else -(1 / 2 : ℝ)

@[expose]
public def evenNegative {n : ℕ} (ε : Fin n → Bool) : Prop :=
  Even ((Finset.univ.filter fun i => !(ε i)).card)

@[expose]
public noncomputable def basisVector {n : ℕ} (i : Fin n) : Vec n := Pi.single i 1

@[expose]
public noncomputable def dot {n : ℕ} (x y : Vec n) : ℝ := ∑ i, x i * y i

@[expose]
public noncomputable def pairRoots (n : ℕ) : Set (Vec n) :=
  {x | ∃ i j : Fin n, i ≠ j ∧ ∃ s t : ℝ,
    s ∈ ({-1, 1} : Set ℝ) ∧ t ∈ ({-1, 1} : Set ℝ) ∧
      x = s • basisVector i + t • basisVector j}

@[expose]
public noncomputable def signedUnitRoots (n : ℕ) : Set (Vec n) :=
  {x | ∃ i : Fin n, x = basisVector i ∨ x = -basisVector i}

@[expose]
public noncomputable def signedDoubleUnitRoots (n : ℕ) : Set (Vec n) :=
  {x | ∃ i : Fin n, x = 2 • basisVector i ∨ x = -(2 • basisVector i)}

end Theory.AlgebraicGroup.StandardRootSystem
