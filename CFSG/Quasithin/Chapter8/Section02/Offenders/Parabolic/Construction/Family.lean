module

public import CFSG.Quasithin.ChapterE.Defs
public import CFSG.Quasithin.ChapterB.Section06To07.Structure
public import CFSG.Quasithin.Defs
public import BenderSuzuki.Converse.PSL2
public import Theory.SpecificGroups.Suzuki.StandardSubgroups
public import Theory.SpecificGroups.SymplecticFour.RootSubgroup

/-!
# The source family used in Proposition 8.2.2

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Definition
E.2.4 and Hypothesis E.2.8, printed pp.217 and 221 (PDF pp.228 and 232).

The normal core is computed inside the selected subgroup. The three
alternatives retain concrete quotient isomorphisms; the same isomorphism
marks the Borel and, in the symplectic case, both matrix root subgroups.
Roots 0 and 4 are the long and short central positive roots in the ordered
hyperbolic-halves convention. The ambient symplectic condition concerns
O²(H/J), whereas the selected quotient is the full Sp₄, including Sp₄(2).

These are definitions, not existence or recognition theorems. They are kept
in the construction extension until the earlier E.2 witness interface is
available. Its producer is `qt-e02-witnesses`; this module adds no premise
asserting a conclusion of Proposition 8.2.2.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
open Subgroup ChapterE ChapterB
open BenderSuzuki.PFAppendixIII BenderSuzuki.Converse BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.SymplecticFour

variable {G : Type*} [Group G]

/-- The literal core of M ∩ I in I. -/
abbrev localCore (M I : Subgroup G) : Subgroup I := (M.subgroupOf I).normalCore

/-- The star quotient used in E.2.4, before proving that its kernel is O₂(I). -/
abbrev Star (M I : Subgroup G) := I ⧸ localCore M I

/-- Restrict to I and then apply the actual normal-core quotient map. -/
def starImage (M I U : Subgroup G) : Subgroup (Star M I) :=
  (U.subgroupOf I).map (QuotientGroup.mk' (localCore M I))

/-- An intrinsic center embedded back into its containing group. -/
def embeddedCenter {X : Type*} [Group X] (S : Subgroup X) : Subgroup X :=
  (center S).map S.subtype

/-- The two nonsymplectic alternatives of E.2.4. The Suzuki parameter m
denotes field degree 2m+1. The dihedral rotation order is an odd prime power. -/
def RankOneAlternative (X : Type*) [Group X] (N : Subgroup X) (k : ℕ) : Prop :=
  (1 < k ∧ ∃ e : X ≃* PSL2 (BinaryGaloisField k),
    N.map e.toMonoidHom = PBorel (BinaryGaloisField k)) ∨
  (∃ m : ℕ, 0 < m ∧ k = 2 * m + 1 ∧
    ∃ e : X ≃* SuzukiMatrixGroup m,
      N.map e.toMonoidHom = SuzukiBorelSubgroup m) ∨
  (k = 1 ∧ ∃ p a : ℕ, p.Prime ∧ Odd p ∧ 0 < a ∧
    Nonempty (X ≃* DihedralGroup (p ^ a)))

/-- E.2.4(3), including the ambient residual condition and both root
exclusions. In particular this does not replace Sp₄(2) by its derived group. -/
def SymplecticAlternative (Hstar X : Type*) [Group Hstar] [Group X]
    (N S U : Subgroup X) (k : ℕ) : Prop :=
  0 < k ∧
  (∃ n : ℕ, 0 < n ∧
    Nonempty (pResidual 2 Hstar ≃* _root_.commutator (Sp (BinaryGaloisField n)))) ∧
  ∃ e : X ≃* Sp (BinaryGaloisField k),
    N.map e.toMonoidHom = borel ∧ U ≤ embeddedCenter S ∧
    ¬ U.map e.toMonoidHom ≤ RootSubgroup.group 0 ∧
    ¬ U.map e.toMonoidHom ≤ RootSubgroup.group 4

/-- Membership in the genuine family I(H,T,V), retaining its parameter k.
M denotes the ambient M, so its restriction to H is the source !N(T).
The source right conjugate V^h is represented by conjugation with h⁻¹. -/
structure Family [Finite G] (H T M V I : Subgroup G) (k : ℕ) : Prop where
  elementary : IsElementaryAbelian 2 V
  nontrivial : V ≠ ⊥
  le_sylow : V ≤ T
  le_ambient : I ≤ H
  generate : ∃ h ∈ I, V ⊔ V.map (MulAut.conj h⁻¹).toMonoidHom = I
  sylow : ∃ S : Sylow 2 I, (S : Subgroup I) = T.subgroupOf I
  core_two_closed : IsTwoClosed (localCore M I)
  classified : RankOneAlternative (Star M I) (starImage M I M) k ∨
    SymplecticAlternative (Star M H) (Star M I)
      (starImage M I M) (starImage M I T) (starImage M I V) k
  parameter_dvd : k ∣ generationParameter H

/-- The actual hypotheses of E.2.8, expressed inside H while retaining the
original ambient subgroups. No characteristic-two or TI conclusion is built in. -/
structure HypothesisE28 [Finite G] (K : GroupClass) (H T M V : Subgroup G) : Prop where
  le_ambient : T ≤ H
  minimal : ∃ S : Sylow 2 H, (S : Subgroup H) = T.subgroupOf H ∧
    ∃ hP : IsMinimalParabolicOver S ⊤,
      M.subgroupOf H = minimalParabolicMax S hP
  sqtk : IsSQTK K H
  elementary : IsElementaryAbelian 2 V
  le_sylow : V ≤ T
  normal_in_sylow : (V.subgroupOf T).Normal
  le_local_core : V ≤ (pCore 2 (M.subgroupOf H)).map
    (H.subtype.comp (M.subgroupOf H).subtype)
  outside_core : ¬ V ≤ (localCore M H).map H.subtype

end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
