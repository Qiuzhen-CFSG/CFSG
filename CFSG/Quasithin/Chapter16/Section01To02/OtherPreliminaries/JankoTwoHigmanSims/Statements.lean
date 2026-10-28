module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Conventions
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS
public import Theory.GroupTheory.QuaternionCentralProductIntrinsic
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The J₂ and HS centralizer alternatives

These are specifications of the table in Aschbacher–Smith, combined manuscript
of 1 March 2004, 16.1.5(8),(10), printed p.1172. They are not assertions that
the table has been proved. The carriers are the fixed degree-100 ATLAS groups.

An extension is specified by a normal subgroup and an actual isomorphism of
its quotient. No splitting is imposed. Central products retain embeddings of
the factors, their common central involution, commutation, and generation.
In particular Q₈² * C₄ means (Q₈ * Q₈) * C₄, of order 64.

The separate kernel condition records the action needed to exclude components;
an extension shape by itself does not imply that condition. The component
catalogues and Sylow indices are the subsequent obligations in 16.1.7–8.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims

open Subgroup Theory.GroupTheory

abbrev C2 := Multiplicative (ZMod 2)
abbrev C4 := Multiplicative (ZMod 4)
abbrev E4 := Fin 2 → C2
abbrev E16 := Fin 4 → C2
abbrev A5 := alternatingGroup (Fin 5)
abbrev A6 := alternatingGroup (Fin 6)
abbrev A8 := alternatingGroup (Fin 8)
abbrev S5 := Equiv.Perm (Fin 5)
abbrev S8 := Equiv.Perm (Fin 8)
abbrev L3Two := Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)

/-- The exact central product Q₈ * D₈, with the factors embedded in the group. -/
def IsQuaternionDihedralProduct (Q : Type*) [Group Q] : Prop :=
  ∃ B D : Subgroup Q,
    Nonempty (B ≃* QuaternionGroup 2) ∧
    Nonempty (D ≃* DihedralGroup 4) ∧
    Nat.card (B ⊓ D : Subgroup Q) = 2 ∧
    (∀ b ∈ B, ∀ d ∈ D, b * d = d * b) ∧ B ⊔ D = ⊤

/-- The exact central product (Q₈ * Q₈) * C₄. Commutation forces the
intersection into the centers of both factors; its order is two. -/
def IsQuaternionSquareCyclicFourProduct (Q : Type*) [Group Q] : Prop :=
  ∃ B D : Subgroup Q,
    Nonempty (QuaternionCentralProductData B) ∧
    Nonempty (D ≃* C4) ∧
    Nat.card (B ⊓ D : Subgroup Q) = 2 ∧
    (∀ b ∈ B, ∀ d ∈ D, b * d = d * b) ∧ B ⊔ D = ⊤

/-- The source extension A₅/(Q₈ * D₈), without a splitting assertion. -/
def IsJ2CoreExtension (C : Type*) [Group C] : Prop :=
  ∃ (Q : Subgroup C) (_ : Q.Normal),
    IsQuaternionDihedralProduct Q ∧ Nonempty (C ⧸ Q ≃* A5)

/-- The source extension S₅/(Q₈² * C₄), without a splitting assertion. -/
def IsHSCoreExtension (C : Type*) [Group C] : Prop :=
  ∃ (Q : Subgroup C) (_ : Q.Normal),
    IsQuaternionSquareCyclicFourProduct Q ∧ Nonempty (C ⧸ Q ≃* S5)

/-- The other outer HS centralizer, with elementary abelian kernel of order 16. -/
def IsHSElementaryExtension (C : Type*) [Group C] : Prop :=
  ∃ (Q : Subgroup C) (_ : Q.Normal),
    Nonempty (Q ≃* E16) ∧ Nonempty (C ⧸ Q ≃* S5)

/-- The extra kernel-action calculation needed in the extension cases.
It must be proved on the actual fixed subgroup, not inferred from its shape. -/
def HasSelfCentralizingNormalTwoSubgroup (C : Type*) [Group C] : Prop :=
  ∃ (Q : Subgroup C) (_ : Q.Normal),
    IsPGroup 2 Q ∧ centralizer (Q : Set C) ≤ Q

/-- Both inner and outer alternatives of 16.1.5(8). -/
def J2InvolutionAlternative (r : MulAut Sporadic.LeechRelated.J2.Carrier) : Prop :=
  ((∃ g, r = MulAut.conj g) ∧
    (IsJ2CoreExtension r.fixedSubgroup ∨ Nonempty (r.fixedSubgroup ≃* E4 × A5))) ∨
  ((¬ ∃ g, r = MulAut.conj g) ∧ Nonempty (r.fixedSubgroup ≃* MulAut L3Two))

/-- Both inner and outer alternatives of 16.1.5(10). -/
def HSInvolutionAlternative (r : MulAut Sporadic.LeechRelated.HS.Carrier) : Prop :=
  ((∃ g, r = MulAut.conj g) ∧
    (IsHSCoreExtension r.fixedSubgroup ∨ Nonempty (r.fixedSubgroup ≃* C2 × MulAut A6))) ∨
  ((¬ ∃ g, r = MulAut.conj g) ∧
    (Nonempty (r.fixedSubgroup ≃* S8) ∨ IsHSElementaryExtension r.fixedSubgroup))

/-- Actual component isomorphisms in the J₂ cases of 16.1.7. -/
def IsJ2CentralizerComponent (K : Type*) [Group K] : Prop :=
  Nonempty (K ≃* A5) ∨ Nonempty (K ≃* L3Two)

/-- Actual component isomorphisms in the HS cases of 16.1.7. -/
def IsHSCentralizerComponent (K : Type*) [Group K] : Prop :=
  Nonempty (K ≃* A6) ∨ Nonempty (K ≃* A8)

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims
