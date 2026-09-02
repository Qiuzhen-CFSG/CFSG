module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Theory.Comparator.Defs
public import Theory.Quasithin
public import FeitThompson.Gorenstein.Chapter8_2
public import FeitThompson.PCore.PCore
public import FeitThompson.PGroup.Omega


/-!
# Stellmacher's main theorems

This module pins the statements of Theorems 1 and 2 from
`refs/latex/stellmacher-n-group.tex`, lines 108--131.  The auxiliary
definitions make explicit the terminology used in the statements and their
introductory explanation at lines 69--145.
-/

universe u

namespace Stellmacher

/-- The source's `(N₂)` condition: every 2-local subgroup is solvable. -/
@[expose] public def IsNTwoGroup (H : Type u) [Group H] [Finite H] : Prop :=
  ∀ U : Subgroup H, Theory.Quasithin.IsTwoLocal U → Group.IsSolvable U

/-- Model witnesses used by the shared interface for the four local types in
alternative (a) of Theorem 2.

`L₃(2)` is represented by the standard projective special linear group and
`Sp₄(2)` by its isomorphic copy `S₆`.  No concrete group model for
`G₂(2)'` or `²F₄(2)'` is available in the imported API, so those two
constructors retain the standard simple-group order signatures as explicit
surrogates.  The local-amalgam predicate below, rather than an ambient group
isomorphism, is the formal interface for the source's phrase “of type”. -/
public inductive IsExceptionalModel
    (X : Type u) [Group X] [Finite X] : Prop
  | linearThreeTwo
      (_ : Nonempty
        (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)))
  | symplecticFourTwo (_ : Nonempty (X ≃* Equiv.Perm (Fin 6)))
  | gTwoTwoDerived (_ : IsSimpleGroup X) (_ : Nat.card X = 6048)
  | twistedF4TwoDerived
      (_ : IsSimpleGroup X) (_ : Nat.card X = 17971200)

/-- Concrete identification of a group underlying one of the eight local
types in Theorem 1.

The first constructor incorporates the four models in Theorem 2.  The
remaining identifications use `Ω₆⁺(2) ≃ A₈` and
`Ω₆⁺(3) ≃ PSL₄(3)`; `M₁₂` and `Ω₆⁻(3) ≃ PSU₄(3)` are
characterized by their standard simple-group orders. -/
public inductive IsMainTheoremModel
    (X : Type u) [Group X] [Finite X] : Prop
  | exceptional (_ : IsExceptionalModel X)
  | mathieuTwelve (_ : IsSimpleGroup X) (_ : Nat.card X = 95040)
  | omegaSixPlusTwo (_ : Nonempty (X ≃* alternatingGroup (Fin 8)))
  | omegaSixMinusThree (_ : IsSimpleGroup X) (_ : Nat.card X = 3265920)
  | omegaSixPlusThree
      (_ : Nonempty
        (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3)))

/-- Data expressing the source's local meaning of "`H` is of type `X`".

The group `X₀` is represented as a subgroup of `Aut(X)` containing every
inner automorphism, with injective inner-automorphism map.  The pairs
`(P1, P2)` and `(Q1, Q2)` are isomorphic as amalgams: their two isomorphisms
agree on `P1 ⊓ P2` and map it onto `Q1 ⊓ Q2`.  The `Qᵢ` are distinct
maximal 2-local subgroups of `X₀`, while `S0 ≤ P1 ⊓ P2` and
`O₂(⟨P1, P2⟩) = 1`, as required in the source's introductory definition. -/
public structure LocalTypeAmalgam
    (Model : ∀ (X : Type u) [Group X] [Finite X], Prop)
    {H : Type u} [Group H] [Finite H] (S0 : Sylow 2 H) where
  X : Type u
  [groupX : Group X]
  [finiteX : Finite X]
  model : Model X
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

/-- The local-amalgam data specialized to the four types in Theorem 2. -/
public abbrev ExceptionalAmalgam
    {H : Type u} [Group H] [Finite H] (S0 : Sylow 2 H) :=
  LocalTypeAmalgam IsExceptionalModel S0

/-- The source's phrase that `H` is of type `L₃(2)`, `Sp₄(2)`,
`G₂(2)'`, or `²F₄(2)'`.

The paper gives the full type-specific local conditions later (Sections
8--10).  The shared interface here records the common local-amalgam data
from the introductory definition; it deliberately does not identify `H`
with the named simple group. -/
@[expose] public def IsOfExceptionalType
    {H : Type u} [Group H] [Finite H] (S0 : Sylow 2 H) : Prop :=
  Nonempty (ExceptionalAmalgam S0)

/-- The source's phrase that `H` is of one of the eight local types in
Theorem 1. -/
@[expose] public def IsOfMainTheoremType
    {H : Type u} [Group H] [Finite H] (S0 : Sylow 2 H) : Prop :=
  Nonempty (LocalTypeAmalgam IsMainTheoremModel S0)

/-- The Baumann subgroup
`B = C_{S₀}(Ω₁(Z(J(S₀))))`, viewed as a subgroup of the ambient group. -/
@[expose] public def baumannSubgroup
    {H : Type u} [Group H] (S0 : Sylow 2 H) : Subgroup H :=
  let ZJ := thompsonCenter (G := H) (S0 : Subgroup H)
  (S0 : Subgroup H) ⊓
    Subgroup.centralizer
      (((omega₁ (G := ZJ) (p := 2)).map ZJ.subtype : Subgroup H) : Set H)

/-- A subgroup `U` is of characteristic 2 type when
`C_U(O₂(U)) ≤ O₂(U)`. -/
@[expose] public def IsCharacteristicTwoType
    {H : Type u} [Group H] (U : Subgroup H) : Prop :=
  Subgroup.centralizer (pCore 2 U : Set U) ≤ pCore 2 U

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

/-- **Stellmacher, Theorem 1.**

Let `S0` be a Sylow 2-subgroup of the finite group `H`, and let `B` be its
Baumann subgroup.  If every 2-local subgroup containing `B` is solvable and
of characteristic 2 type, and at least two distinct maximal 2-local
subgroups contain `S0`, then `H` has one of the eight local types listed in
the source.

Source: `refs/latex/stellmacher-n-group.tex`, lines 108--118. -/
public theorem theorem_one
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H)
    (hlocal : ∀ U : Subgroup H,
      Theory.Quasithin.IsTwoLocal U →
      baumannSubgroup S0 ≤ U →
      Group.IsSolvable U ∧ IsCharacteristicTwoType U)
    (hmax : ∃ P1 P2 : Subgroup H,
      P1 ≠ P2 ∧
      Theory.Quasithin.IsMaximalTwoLocal P1 ∧
      Theory.Quasithin.IsMaximalTwoLocal P2 ∧
      (S0 : Subgroup H) ≤ P1 ∧
      (S0 : Subgroup H) ≤ P2) :
    IsOfMainTheoremType S0 := by
  sorry

/-- **Stellmacher, Theorem 2.**

If `H` is an `(N₂)`-group of even order and `S0` is a Sylow 2-subgroup
of `H`, then one of the following holds: `H` has one of the four exceptional
local types; `S0` is dihedral or semidihedral; `S0` has order `2⁵` and `H`
has a maximal 2-local subgroup isomorphic to `C₂ × S₄`; `H` has a
strongly embedded subgroup; or some 2-local subgroup has nontrivial
`2'`-core.

Source: `refs/latex/stellmacher-n-group.tex`, lines 121--131; the journal
scan `refs/files/stellmacher-n-group.pdf`, p. 12, resolves the `2'`-core
notation in clause (e). -/
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
      Theory.Quasithin.IsTwoLocal U ∧ pPrimeCore 2 U ≠ ⊥) := by
  sorry

end Stellmacher
