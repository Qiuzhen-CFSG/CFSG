module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Theory.Comparator.Defs
public import Theory.Quasithin
public import FeitThompson.Gorenstein.Chapter8_2
public import FeitThompson.PCore.PCore
public import Theory.GroupTheory.PGroup.Omega
public import Stellmacher.ElementaryAbelianMaxDefs


/-!
# Shared definitions for Stellmacher's main theorems

This module owns the terminology shared by Theorems 1 and 2 and by the
numbered sections that build their proofs.  It formalizes the `(N₂)` condition,
the legacy model-amalgam interface, the source Baumann subgroup and
characteristic 2 type, and the dihedral and semidihedral alternatives from
`refs/latex/stellmacher-n-group.tex`, lines 69--145.

Keeping these definitions below the numbered section modules lets those
modules use the theorem statements' terminology without importing the final
theorem module back into the proof graph. The Baumann subgroup uses the
elementary Thompson subgroup specified in
Section 2; its shared definitions are re-exported from
`Stellmacher.ElementaryAbelianMaxDefs`. The concrete four-type predicate
for Theorem 2 is defined above the graph notation in
`Stellmacher.ExceptionalType`; the full eight-type boundary is defined in
`Stellmacher.MainType`.
-/

universe u

namespace Stellmacher

/-- The source's `(N₂)` condition: every 2-local subgroup is solvable. -/
@[expose] public def IsNTwoGroup (H : Type u) [Group H] [Finite H] : Prop :=
  ∀ U : Subgroup H, IsTwoLocal U → Group.IsSolvable U

/-- Model witnesses used by the generic Theorem 1 type interface.

`L₃(2)` is represented by the standard projective special linear group and
`Sp₄(2)` by its isomorphic copy `S₆`.  No concrete group model for
`G₂(2)'` or `²F₄(2)'` is available in the imported API, so those two
constructors retain the standard simple-group order signatures inside the
broader eight-model classification.  Theorem 2's source-local definitions are
given separately in `Stellmacher.ExceptionalType`. -/
public inductive IsExceptionalModel
    (X : Type u) [Group X] [Finite X] : Prop
  | linearThreeTwo
      (_ : Nonempty
        (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)))
  | symplecticFourTwo (_ : Nonempty (X ≃* Equiv.Perm (Fin 6)))
  | gTwoTwoDerived (_ : IsSimpleGroup X) (_ : Nat.card X = 6048)
  | twistedF4TwoDerived
      (_ : IsSimpleGroup X) (_ : Nat.card X = 17971200)

/-- Legacy model catalogue retained for explicit model-amalgam work.

The first constructor incorporates the four models in Theorem 2.  The
remaining identifications use `Ω₆⁺(2) ≃ A₈` and
`Ω₆⁺(3) ≃ PSL₄(3)`; `M₁₂` and `Ω₆⁻(3) ≃ PSU₄(3)` are
characterized by their standard simple-group orders. This catalogue does not
define the source-local conclusion of Theorem 1: its historical last entry is
`PSL₄(3)`, whereas the source's eighth local type is `Ω₈⁺(3)`. The canonical
local types are defined separately in `Stellmacher.MainType`; no model
recognition theorem is asserted by this catalogue. -/
public inductive IsMainTheoremModel
    (X : Type u) [Group X] [Finite X] : Prop
  | exceptional (_ : IsExceptionalModel X)
  | mathieuTwelve (_ : IsSimpleGroup X) (_ : Nat.card X = 95040)
  | omegaSixPlusTwo (_ : Nonempty (X ≃* alternatingGroup (Fin 8)))
  | omegaSixMinusThree (_ : IsSimpleGroup X) (_ : Nat.card X = 3265920)
  | omegaSixPlusThree
      (_ : Nonempty
        (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3)))

/-- An explicit comparison with a model amalgam, separate from the precise
source-local configurations used by the classification theorems.

The group `X₀` is represented as a subgroup of `Aut(X)` containing every
inner automorphism, with injective inner-automorphism map.  The pairs
`(P1, P2)` and `(Q1, Q2)` are isomorphic as amalgams: their two isomorphisms
agree on `P1 ⊓ P2` and map it onto `Q1 ⊓ Q2`.  The `Qᵢ` are distinct
maximal 2-local subgroups of `X₀`, while `S0 ≤ P1 ⊓ P2` and
`O₂(⟨P1, P2⟩) = 1`. Establishing this comparison from a source-local
configuration would require additional recognition theorems. -/
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
  Q1_maximal_twoLocal : IsMaximalTwoLocal Q1
  Q2_maximal_twoLocal : IsMaximalTwoLocal Q2
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

/-- The separate explicit model-amalgam condition from the earlier interface.
This is not identified with the paper's eight source-local configurations. -/
@[expose] public def HasMainModelAmalgam
    {H : Type u} [Group H] [Finite H] (S0 : Sylow 2 H) : Prop :=
  Nonempty (LocalTypeAmalgam IsMainTheoremModel S0)

/-- The source Baumann subgroup `C_{S₀}(Ω₁(Z(J(S₀))))`, using the
subgroup J generated by elementary abelian subgroups of largest order.
Section 2 (printed p.19) specifies this J; the all-abelian Thompson subgroup
used in the earlier transcription is a different construction. -/
@[expose] public noncomputable def baumannSubgroup
    {H : Type u} [Group H] (S0 : Sylow 2 H) : Subgroup H :=
  let J := elementaryAbelianMaxJ (G := H) (S0 : Subgroup H)
  (S0 : Subgroup H) ⊓
    Subgroup.centralizer
      (((omega₁ (G := Subgroup.center J) (p := 2)).map
        (Subgroup.center J).subtype).map J.subtype : Set H)

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

end Stellmacher
