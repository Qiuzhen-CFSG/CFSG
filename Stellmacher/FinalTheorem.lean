module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Theory.Comparator.Defs
public import Theory.Quasithin
public import FeitThompson.PCore.PCore

/-!
# Stellmacher's Theorem 2

This module pins the statement of Theorem 2 from
`refs/latex/stellmacher-n-group.tex`, lines 121--131.  The auxiliary
definitions make explicit the terminology used in the statement and its
introductory explanation at lines 69--140.
-/

universe u

namespace Stellmacher

/-- The source's `(N₂)` condition: every 2-local subgroup is solvable. -/
@[expose] public def IsNTwoGroup (H : Type u) [Group H] [Finite H] : Prop :=
  ∀ U : Subgroup H, Theory.Quasithin.IsTwoLocal U → Group.IsSolvable U

/-- Concrete identification of a group underlying one of the four local
types in alternative (a) of Theorem 2.

Here `Sp₄(2)` is represented by its standard isomorphic copy `S₆`.  The
two remaining simple groups are characterized by their standard orders:
`|G₂(2)'| = 6048` and `|²F₄(2)'| = 17971200`. -/
public inductive IsExceptionalModel
    (X : Type u) [Group X] [Finite X] : Prop
  | linearThreeTwo
      (_ : Nonempty
        (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)))
  | symplecticFourTwo (_ : Nonempty (X ≃* Equiv.Perm (Fin 6)))
  | gTwoTwoDerived (_ : IsSimpleGroup X) (_ : Nat.card X = 6048)
  | twistedF4TwoDerived
      (_ : IsSimpleGroup X) (_ : Nat.card X = 17971200)

/-- Data expressing the source's local meaning of "`H` is of type `X`".

The group `X₀` is represented as a subgroup of `Aut(X)` containing every
inner automorphism, with injective inner-automorphism map.  The pairs
`(P1, P2)` and `(Q1, Q2)` are isomorphic as amalgams: their two isomorphisms
agree on `P1 ⊓ P2` and map it onto `Q1 ⊓ Q2`.  The `Qᵢ` are distinct
maximal 2-local subgroups of `X₀`, while `S0 ≤ P1 ⊓ P2` and
`O₂(⟨P1, P2⟩) = 1`, as required in the source's introductory definition. -/
public structure ExceptionalAmalgam
    {H : Type u} [Group H] [Finite H] (S0 : Sylow 2 H) where
  X : Type u
  [groupX : Group X]
  [finiteX : Finite X]
  model : IsExceptionalModel X
  X0 : Subgroup (MulAut X)
  inner_injective : Function.Injective (fun x : X ↦ MulAut.conj x)
  inner_le : ∀ x : X, MulAut.conj x ∈ X0
  Q1 : Subgroup X0
  Q2 : Subgroup X0
  Q1_ne_Q2 : Q1 ≠ Q2
  Q1_maximal_twoLocal : Theory.Quasithin.IsMaximalTwoLocal Q1
  Q2_maximal_twoLocal : Theory.Quasithin.IsMaximalTwoLocal Q2
  P1 : Subgroup H
  P2 : Subgroup H
  S0_le : (S0 : Subgroup H) ≤ P1 ⊓ P2
  P1_twoCore_ne_bot : pCore 2 P1 ≠ ⊥
  P2_twoCore_ne_bot : pCore 2 P2 ≠ ⊥
  join_twoCore_eq_bot : pCore 2 ↑(P1 ⊔ P2) = ⊥
  e1 : P1 ≃* Q1
  e2 : P2 ≃* Q2
  compatible : ∀ (x : H) (hx1 : x ∈ P1) (hx2 : x ∈ P2),
    ((e1 ⟨x, hx1⟩ : Q1) : X0) = ((e2 ⟨x, hx2⟩ : Q2) : X0)
  intersection_surjective : ∀ (y : X0), y ∈ Q1 → y ∈ Q2 →
    ∃ (x : H) (hx1 : x ∈ P1) (hx2 : x ∈ P2),
      ((e1 ⟨x, hx1⟩ : Q1) : X0) = y ∧
      ((e2 ⟨x, hx2⟩ : Q2) : X0) = y

/-- The source's phrase that `H` is of type `L₃(2)`, `Sp₄(2)`,
`G₂(2)'`, or `²F₄(2)'`. -/
@[expose] public def IsOfExceptionalType
    {H : Type u} [Group H] [Finite H] (S0 : Sylow 2 H) : Prop :=
  Nonempty (ExceptionalAmalgam S0)

/-- A group is dihedral when it is isomorphic to a polygonal dihedral
group. -/
@[expose] public def IsDihedralGroup (G : Type*) [Group G] : Prop :=
  ∃ n : ℕ, Nonempty (G ≃* DihedralGroup n)

/-- The standard presentation of a semidihedral group of order `2^n`, for
`n ≥ 4`. -/
@[expose] public def IsSemidihedralGroup (G : Type*) [Group G] : Prop :=
  ∃ n : ℕ, 4 ≤ n ∧ Nat.card G = 2 ^ n ∧
    ∃ a b : G,
      orderOf a = 2 ^ (n - 1) ∧
      orderOf b = 2 ∧
      b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1) ∧
      Subgroup.closure ({a, b} : Set G) = ⊤

/-- **Stellmacher, Theorem 2.**

If `H` is an `(N₂)`-group of even order and `S0` is a Sylow 2-subgroup
of `H`, then one of the following holds: `H` has one of the four exceptional
local types; `S0` is dihedral or semidihedral; `S0` has order `2⁵` and `H`
has a maximal 2-local subgroup isomorphic to `C₂ × S₄`; `H` has a
strongly embedded subgroup; or some 2-local subgroup has nontrivial 2-core.

Source: `refs/latex/stellmacher-n-group.tex`, lines 121--131. -/
public theorem theorem_two
    {H : Type u} [Group H] [Finite H]
    (hN2 : IsNTwoGroup H) (hEven : Even (Nat.card H))
    (S0 : Sylow 2 H) :
    IsOfExceptionalType S0 ∨
    (IsDihedralGroup S0 ∨ IsSemidihedralGroup S0) ∨
    (Nat.card S0 = 2 ^ 5 ∧
      ∃ U : Subgroup H,
        Theory.Quasithin.IsMaximalTwoLocal U ∧
        Nonempty (U ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))) ∨
    (∃ M : Subgroup H, Theory.Comparator.IsStronglyEmbedded M) ∨
    (∃ U : Subgroup H,
      Theory.Quasithin.IsTwoLocal U ∧ pCore 2 U ≠ ⊥) := by
  sorry

end Stellmacher
