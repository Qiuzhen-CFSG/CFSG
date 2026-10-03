module

public import ABG.ChapterII.Section1.WreathedDefs
public import BenderSuzuki.External.Hall.Basic
public import FeitThompson.BGsection1.Defs

/-!
# The full source fusion alternatives

ABG Chapter II §1 Propositions 1 and 2 (article pp10–12) state four fusion
alternatives for quasi-dihedral and wreathed Sylow two-subgroups. This module
translates every clause of those alternatives, without asserting any of them.
The chosen four or abelian subgroup and quaternion central product are retained
in a frame so the normalizer conclusions concern those same subgroups.

Conjugacy counts contain representatives, coverage and pairwise inequivalence.
The quaternion denominator is VC(V), not merely C(V), as confirmed by the scan;
its index is recorded using ambient subgroup relative index. The Q patterns
retain normality, the index of K, its generalized quaternion Sylow subgroup,
and the specified weak closure. The wreathed D pattern retains the actual
inclusion of U as a Sylow subgroup of K. Existing weak-closure and normal
p-complement definitions are reused rather than redefined.

These exposed predicates form the common interface for proving the fusion
propositions and for the source Q/D/QD definitions. In particular the QD
pattern is not replaced by only its no-index-two and involution clauses.
-/

noncomputable section

namespace ABG

universe u

/-- The absence of normal subgroups of index two is part of the source fusion data. -/
@[expose] public def HasNoNormalIndexTwoSubgroup (G : Type u) [Group G] : Prop :=
  ∀ K : Subgroup G, K.Normal → K.index ≠ 2

/-- Exactly `k` conjugacy classes of elements of order `m`, with actual representatives. -/
@[expose] public def HasElementConjugacyClassCount
    (G : Type u) [Group G] (m k : ℕ) : Prop :=
  ∃ r : Fin k → G, (∀ i, orderOf (r i) = m) ∧
    (∀ i j, IsConj (r i) (r j) → i = j) ∧
    ∀ x : G, orderOf x = m → ∃ i, IsConj x (r i)

/-- The center of a subgroup, viewed in its original ambient group. -/
@[expose] public def subgroupCenter {G : Type u} [Group G] (S : Subgroup G) : Subgroup G :=
  (Subgroup.center S).map S.subtype

/-- Every subgroup of the Sylow center is weakly closed, not just the whole center. -/
@[expose] public def HasWeaklyClosedCenterSubgroups
    {G : Type u} [Group G] (S : Subgroup G) : Prop :=
  ∀ Z : Subgroup G, Z ≤ subgroupCenter (S : Subgroup G) → BenderSuzuki.External.WeaklyClosedIn S Z

/-- The automizer index `|N(U):C(U)|`. -/
@[expose] public def automizerIndex {G : Type u} [Group G] (U : Subgroup G) : ℕ :=
  (Subgroup.centralizer (U : Set G)).relIndex (Subgroup.normalizer (U : Set G))

/-- The outer automizer index `|N(V):VC(V)|`; the factor `V` is essential. -/
@[expose] public def outerAutomizerIndex {G : Type u} [Group G] (V : Subgroup G) : ℕ :=
  (V ⊔ Subgroup.centralizer (V : Set G)).relIndex (Subgroup.normalizer (V : Set G))

/-- The choices in quasi-dihedral Proposition II.1.1. The unique conjugacy
classes of these subgroups are proved by Lemma II.1.1(ii). -/
@[expose] public def QuasiDihedralFusionFrame
    {G : Type u} [Group G] (S : Sylow 2 G) (T Q : Subgroup G) : Prop :=
  Stellmacher.IsSemidihedralGroup S ∧ T ≤ S ∧ Q ≤ S ∧ IsFourGroup T ∧ IsQuaternionGroup Q

/-- The choices in wreathed Proposition II.1.2: the unique abelian maximal
subgroup and a central product of a quaternion subgroup with the Sylow center. -/
@[expose] public def WreathedFusionFrame
    {G : Type u} [Group G] (S : Sylow 2 G) (n : ℕ) (U V : Subgroup G) : Prop :=
  IsWreathedOfHeight S n ∧ U ≤ S ∧ IsMulCommutative U ∧
    IsCoatom (U.subgroupOf S) ∧
    (∀ W : Subgroup S, IsMulCommutative W → IsCoatom W → W = U.subgroupOf S) ∧
    ∃ Q : Subgroup G, Q ≤ S ∧ IsQuaternionGroup Q ∧ V = Q ⊔ subgroupCenter (S : Subgroup G)

/-- All clauses of Proposition II.1.1(i). -/
@[expose] public def QuasiDihedralQDPattern
    {G : Type u} [Group G] (T Q : Subgroup G) : Prop :=
  HasNoNormalIndexTwoSubgroup G ∧ HasElementConjugacyClassCount G 2 1 ∧
    HasElementConjugacyClassCount G 4 1 ∧ automizerIndex T = 6 ∧ outerAutomizerIndex Q = 6

/-- All clauses of Proposition II.1.1(ii). -/
@[expose] public def QuasiDihedralQPattern
    {G : Type u} [Group G] (S : Sylow 2 G) (T Q : Subgroup G) : Prop :=
  (∃ K : Subgroup G, K.Normal ∧ K.index = 2 ∧ HasGeneralizedQuaternionSylowTwo K ∧
    HasNoNormalIndexTwoSubgroup K) ∧
  BenderSuzuki.External.WeaklyClosedIn S (subgroupCenter (S : Subgroup G)) ∧
    HasElementConjugacyClassCount G 2 2 ∧ HasElementConjugacyClassCount G 4 1 ∧
      automizerIndex T = 2 ∧ outerAutomizerIndex Q = 6

/-- All clauses of Proposition II.1.1(iii). -/
@[expose] public def QuasiDihedralDPattern
    {G : Type u} [Group G] (T Q : Subgroup G) : Prop :=
  (∃ K : Subgroup G, K.Normal ∧ K.index = 2 ∧ HasDihedralSylowTwo K ∧
    HasNoNormalIndexTwoSubgroup K) ∧
  HasElementConjugacyClassCount G 2 1 ∧ HasElementConjugacyClassCount G 4 2 ∧
    automizerIndex T = 6 ∧ outerAutomizerIndex Q = 2

/-- All clauses of Proposition II.1.1(iv). -/
@[expose] public def QuasiDihedralNormalComplementPattern
    {G : Type u} [Group G] (T Q : Subgroup G) : Prop :=
  HasNormalPComplement 2 G ∧ HasElementConjugacyClassCount G 2 2 ∧
    HasElementConjugacyClassCount G 4 2 ∧ automizerIndex T = 2 ∧ outerAutomizerIndex Q = 2

/-- All clauses of Proposition II.1.2(i). -/
@[expose] public def WreathedQDPattern
    {G : Type u} [Group G] (U V : Subgroup G) : Prop :=
  HasNoNormalIndexTwoSubgroup G ∧ HasElementConjugacyClassCount G 2 1 ∧
    automizerIndex U = 6 ∧ outerAutomizerIndex V = 6

/-- All clauses of Proposition II.1.2(ii), including the height-dependent index. -/
@[expose] public def WreathedQPattern
    {G : Type u} [Group G] (S : Sylow 2 G) (n : ℕ) (U V : Subgroup G) : Prop :=
  (∃ K : Subgroup G, K.Normal ∧ K.index = 2 ^ n ∧ HasGeneralizedQuaternionSylowTwo K ∧
    HasNoNormalIndexTwoSubgroup K) ∧
  HasWeaklyClosedCenterSubgroups (S : Subgroup G) ∧ HasElementConjugacyClassCount G 2 2 ∧
    automizerIndex U = 2 ∧ outerAutomizerIndex V = 6

/-- All clauses of Proposition II.1.2(iii). The chosen `U` itself is the Sylow
subgroup of the normal subgroup, via its actual inclusion in `G`. -/
@[expose] public def WreathedDPattern
    {G : Type u} [Group G] (U V : Subgroup G) : Prop :=
  (∃ K : Subgroup G, K.Normal ∧ HasNoNormalIndexTwoSubgroup K ∧
    ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = U) ∧
  HasElementConjugacyClassCount G 2 2 ∧ automizerIndex U = 6 ∧ outerAutomizerIndex V = 2

/-- All clauses of Proposition II.1.2(iv). -/
@[expose] public def WreathedNormalComplementPattern
    {G : Type u} [Group G] (U V : Subgroup G) : Prop :=
  HasNormalPComplement 2 G ∧ HasElementConjugacyClassCount G 2 3 ∧
    automizerIndex U = 2 ∧ outerAutomizerIndex V = 2

end ABG
