module

public import BenderSuzuki.ZD.Recognition.Basic
public import BenderSuzuki.SE.Interfaces
public import BenderSuzuki.SE.Section9Focal

/-!
# The statement and induction boundary of Theorem ZD

The conclusion records every clause of GLS, Volume 4, Chapter 2, Theorem ZD,
including the internal direct product, the Borel subgroup in the derived
factor, and the location of the odd core. The two factors of the quotient
are specified by generation, trivial intersection, and elementwise commuting.

The minimal-counterexample record is an induction hypothesis, not a source
theorem. `SimpleReduction` records the output of Sections 3–4 which feeds
the residual strong-embedding argument of Sections 5–17. Final assembly must
discharge both reductions.
-/

noncomputable section

namespace BenderSuzuki.ZD

open Theory.GroupTheory PFAppendixIII PFchapter1section1

universe u

/-- All five structural clauses of Theorem ZD, inside `L = ⟨Z⟩` and its
quotient by the odd core. The Borel subgroup is the image of `M ∩ [L,L]`
viewed as a subgroup of the quotient's derived subgroup. -/
@[expose] public def StructureConclusion
    {G : Type u} [Group G] [Finite G] (Z : Set G) (M : Subgroup G) : Prop :=
  let L := Subgroup.closure Z
  let O := pPrimeCore 2 L
  let Q := L ⧸ O
  let q := QuotientGroup.mk' O
  let X := commutator Q
  ∃ u : L,
    (u : G) ∈ M ∧ u ^ 2 = 1 ∧
    commutator L ⊔ Subgroup.zpowers u = ⊤ ∧
    X ⊔ Subgroup.zpowers (q u) = ⊤ ∧
    Disjoint X (Subgroup.zpowers (q u)) ∧
    (∀ x ∈ X, ∀ v ∈ Subgroup.zpowers (q u), Commute x v) ∧
    IsSimpleBenderGroup X ∧
    O ≤ M.comap L.subtype ⊓ commutator L ∧
    IsBorelSubgroup
      (((M.comap L.subtype ⊓ commutator L).map q).subgroupOf X) ∧
    (∀ z : L, (z : G) ∈ Z →
      (q u)⁻¹ * q z ∈ X ∧ q z ≠ q u)

/-- The rank-one alternative is expressed as absence of an elementary four;
nonemptiness of `Z` supplies the nonzero rank in applications. -/
@[expose] public def Conclusion
    {G : Type u} [Group G] [Finite G] (Z : Set G) (M : Subgroup G) : Prop :=
  ¬ TwoRankAtLeastTwo (Subgroup.closure Z) ∨ StructureConclusion Z M

/-- A counterexample together with the all-smaller-groups induction
hypothesis. Quotient groups as well as proper subgroups are covered. -/
public structure MinimalCounterexample
    {G : Type u} [Group G] [Finite G] (Z : Set G) (M : Subgroup G) : Prop where
  disconnected : IsProductDisconnected Z M
  fails : ¬ Conclusion Z M
  smaller : ∀ {H : Type u} [Group H] [Finite H],
    Nat.card H < Nat.card G → ∀ (W : Set H) (N : Subgroup H),
      IsProductDisconnected W N → Conclusion W N

/-- The conclusions of GLS Chapter 2, Theorem 1 and (3B). The fusion clause
uses an ambient Sylow subgroup contained in `M`; this also states that `M`
contains a Sylow subgroup of the ambient group. The remaining clauses say
that `Z` is a class of 2-central involutions and assert Definition SZ(d). -/
public structure SimpleReduction
    {G : Type u} [Group G] [Finite G] (Z : Set G) (M : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  generated : Subgroup.closure Z = ⊤
  one_class : ∀ x ∈ Z, ∀ z ∈ Z, IsConj x z
  two_central : ∀ z ∈ Z, ∃ S : Sylow 2 G,
    z ∈ S ∧ ∀ s : S, Commute z (s : G)
  fusion : ∃ S : Sylow 2 G,
    (S : Subgroup G) ≤ M ∧ ControlsFusionIn M (S : Subgroup G)
  local_embedding : ∀ H : Subgroup G, H ≠ ⊤ → ¬ H ≤ M →
    (∃ z ∈ Z, z ∈ H ∧ z ∈ M) →
    IsStronglyEmbedded
      ((M.comap H.subtype).comap
        (Subgroup.closure (H.subtype ⁻¹' Z)).subtype)

end BenderSuzuki.ZD
