module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.OutsideGeometry
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.Actor

/-!+# Earlier source implications for the solvable outside-core branch

These are universal theorem parameters, not assertions of the earlier results.
`EarlierB685` is B.6.8(5), with the Sylow subgroup of the actual normal core
identified with O₂(H). `Configuration` is Hypothesis E.2.8 in ambient subgroup
coordinates. `SolvableMember` retains the part of Definition E.2.4 used here:
generation by two actual conjugates, the prescribed Sylow intersection,
two-closedness, and an isomorphism of the literal quotient to D₂pᵃ.

`EarlierE29Solvable` is the solvable restriction of E.2.9's existence and
generalized-Fitting inheritance. In this restriction only case (2) of E.2.4
can occur: the rank-one groups with k > 1 and Sp₄(2ᵏ), including Sp₄(2) = S₆,
are nonsolvable. Here k = 1, so the divisibility condition on n(H) is automatic.
We do not assert the full E.2.4 family or its unused nonsolvable alternatives.
In particular, neither the order of the image of V nor any module bound is
part of these parameters. Their source producers remain qt-b0607-structure
and qt-e02-witnesses (under qt-e-02).

Source: Aschbacher–Smith, B.6.8(5), printed pp.113–114; Definition E.2.4 and
E.2.8–11, printed pp.217, 221–224; application in 15.4.2(4), printed p.1156.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.RatioSource.OutsideWitness
universe u

/-- The universal Sylow assertion in B.6.8(5), with its actual embedding. -/
def EarlierB685 : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (H N : Subgroup X),
    ChapterB.IsMinimalParabolicOver T H → (T : Subgroup X) ≤ N → N ⋖ H →
    ∃ S : Sylow 2 (N.subgroupOf H).normalCore,
      (S : Subgroup (N.subgroupOf H).normalCore).Normal ∧
      (S : Subgroup (N.subgroupOf H).normalCore).map
        (N.subgroupOf H).normalCore.subtype = pCore 2 H

variable {X : Type u} [Group X]

/-- E.2.8, with relative normality and the original maximal-subgroup core. -/
structure Configuration (T : Sylow 2 X) (H N V : Subgroup X) : Prop where
  minimal : ChapterB.IsMinimalParabolicOver T H
  sylow_le_maximal : (T : Subgroup X) ≤ N
  maximal : N ⋖ H
  sqtk : IsSQTK KnownSimple.IsKnownSimple H
  elementary : IsElementaryAbelian 2 V
  le_sylow : V ≤ (T : Subgroup X)
  normal_in_sylow : (V.subgroupOf (T : Subgroup X)).Normal
  le_core : V ≤ N.pCoreIn 2
  outside : ¬ V ≤ (N.subgroupOf H).normalCore.map H.subtype

/-- The solvable case of E.2.4, retaining an actual quotient isomorphism.
Conjugation is x ↦ g*x*g⁻¹, so g is the inverse of the book's conjugator. -/
structure SolvableMember (T : Sylow 2 X) (H N V I : Subgroup X) where
  le_H : I ≤ H
  le_I : V ≤ I
  sylow : Sylow 2 I
  sylow_eq : (sylow : Subgroup I).map I.subtype = (T : Subgroup X) ⊓ I
  conjugator : I
  generate : V.subgroupOf I ⊔
    (V.subgroupOf I).map (MulAut.conj conjugator).toMonoidHom = ⊤
  core_two_closed : ∃ S : Sylow 2 (N.subgroupOf I).normalCore,
    (S : Subgroup (N.subgroupOf I).normalCore).Normal
  dihedral : ∃ p a : ℕ, p.Prime ∧ p ≠ 2 ∧ 0 < a ∧
    Nonempty ((I ⧸ (N.subgroupOf I).normalCore) ≃* DihedralGroup (p ^ a))

/-- Universal E.2.9 in its solvable branch, including part (2).
This is an explicit earlier theorem input; no instance is asserted. -/
def EarlierE29Solvable : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (H N V : Subgroup X),
    Configuration T H N V → Group.IsSolvable H →
    (∃ I : Subgroup X, Nonempty (SolvableMember T H N V I)) ∧
    (∀ (I : Subgroup X), SolvableMember T H N V I →
      generalizedFitting H = pCore 2 H → generalizedFitting I = pCore 2 I)

end CFSG.Quasithin.Chapter15.Section04.RatioSource.OutsideWitness
