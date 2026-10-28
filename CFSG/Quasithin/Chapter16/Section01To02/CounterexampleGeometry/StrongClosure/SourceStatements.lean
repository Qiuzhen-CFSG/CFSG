module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.IntersectionGenerated
public import Theory.GroupTheory.SetStrongClosure
public import Theory.GroupTheory.SemidihedralStandardModel
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import BenderSuzuki.SE.Basic
public import BenderSuzuki.ZD.Recognition.Interfaces

/-!+# The checked statement of Aschbacher's Lemma 3.4

These are source specifications and an induction boundary, not asserted
theorems. Both normalizers occur in hypothesis (*). The second conclusion
contains actual strong embedding in the normal closure of A₁. The third
retains the conjugator fused into A₁, the model isomorphism and the order-two
intersection. The rank hypotheses mean the existence of elementary four-groups.

`FusionConclusion` isolates the fusion work in (a)–(g) and the last paragraph
of the proof. Its unique-conjugate-membership assertions explicitly exclude
the identity. The terminal argument must derive the source alternatives
using the exact five-clause ZD theorem, not an assumed Lemma 3.4.

Source: M. Aschbacher, *On finite groups of component type*, Illinois J. Math.
19 (1975), 87–115, Lemma 3.4, pp.94–96, DOI 10.1215/ijm/1256050927.
The publisher PDF was retrieved through Google's public document viewer and
these three pages were visually checked on 5 October 2026. A preserved copy
is in the originating attempt's `Scratch/Asc75StrongClosure/asc75.pdf`.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
universe u

/-- The actual dihedral and semidihedral two-group models. The dihedral
case includes the four-group; the semidihedral model starts at order sixteen. -/
def DihedralOrSemidihedral (A : Type u) [Group A] : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ Nonempty (A ≃* DihedralGroup (2 ^ n))) ∨
  ∃ (n : ℕ) (hn : 4 ≤ n), Nonempty (A ≃* Semidihedral.StandardModel n hn)

/-- Hypothesis (*) and the standing assumptions of Lemma 3.4. -/
structure Hypotheses {G : Type u} [Group G] (S : Sylow 2 G)
    (A₁ A₂ : Subgroup G) : Prop where
  left_le : A₁ ≤ S
  right_le : A₂ ≤ S
  commute : ⁅A₁, A₂⁆ = ⊥
  left_rank : TwoRankAtLeastTwo A₁
  right_rank : TwoRankAtLeastTwo A₂
  closed_in_generated : IsStronglyClosedSet ((A₁ : Set G) ∪ A₂)
    (intersectionGenerated A₁ A₂ ⊓ (S : Subgroup G)) (intersectionGenerated A₁ A₂)
  closed_in_left_normalizer : IsStronglyClosedSet ((A₁ : Set G) ∪ A₂)
    ((S : Subgroup G) ⊓ normalizer (A₁ : Set G)) ⊤
  closed_in_right_normalizer : IsStronglyClosedSet ((A₁ : Set G) ∪ A₂)
    ((S : Subgroup G) ⊓ normalizer (A₂ : Set G)) ⊤

/-- All clauses of alternative (3), with right conjugation throughout. -/
def Exceptional {G : Type u} [Group G] (A₁ A₂ : Subgroup G) : Prop :=
  (∃ g : G, conjugate A₁ g = A₂ ∧ ∃ k : G, k⁻¹ * g * k ∈ A₁) ∧
  DihedralOrSemidihedral A₁ ∧ Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2

/-- All three alternatives in Lemma 3.4, including the strong-embedding
clause in the nested case, inside the genuine normal closure. -/
def Conclusion {G : Type u} [Group G] [Finite G] (A₁ A₂ : Subgroup G) : Prop :=
  intersectionGenerated A₁ A₂ = ⊤ ∨
  ((A₁ ≤ A₂ ∨ A₂ ≤ A₁) ∧ BenderSuzuki.IsStronglyEmbedded
    ((intersectionGenerated A₁ A₂).subgroupOf (normalClosure (A₁ : Set G)))) ∨
  Exceptional A₁ A₂

/-- The exact ZD theorem, universally quantified so it can also be used
inside proper subgroups and quotients. Its proof is owned by the ZD campaign. -/
def TheoremZD : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (Z : Set G) (M : Subgroup G),
    IsProductDisconnected Z M → BenderSuzuki.ZD.Conclusion Z M

/-- The induction hypothesis includes all smaller groups, not just subgroups
of the original group; central quotients are used on pp.95–96. -/
structure MinimalCounterexample {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (A₁ A₂ : Subgroup G) : Prop where
  setup : Hypotheses S A₁ A₂
  fails : ¬ Conclusion A₁ A₂
  smaller : ∀ {X : Type u} [Group X] [Finite X], Nat.card X < Nat.card G →
    ∀ (P : Sylow 2 X) (B₁ B₂ : Subgroup X), Hypotheses P B₁ B₂ → Conclusion B₁ B₂

/-- Having the unique fixed point H in the right-coset action, written as
an exact elementwise conjugate-membership assertion. -/
def UniqueConjugateMembership {G : Type u} [Group G] (H : Subgroup G) (x : G) : Prop :=
  x ∈ H ∧ ∀ g : G, g⁻¹ * x * g ∈ H ↔ g ∈ H

/-- The local-fusion part of the proof before its appeal to Theorem 3.3.
The centralizer assertion (g) follows from unique conjugate membership. -/
structure FusionConclusion {G : Type u} [Group G]
    (S : Sylow 2 G) (A₁ A₂ : Subgroup G) : Prop where
  closed : IsStronglyClosedSet ((A₁ : Set G) ∪ A₂) (S : Subgroup G) ⊤
  unique : ∀ a : G, a ∈ (A₁ : Set G) ∪ A₂ → a ≠ 1 →
    UniqueConjugateMembership (intersectionGenerated A₁ A₂) a
  product_unique : ∀ a₁ ∈ A₁, ∀ a₂ ∈ A₂,
    orderOf a₁ = 2 → orderOf a₂ = 2 → a₁ * a₂ ≠ 1 →
      UniqueConjugateMembership (intersectionGenerated A₁ A₂) (a₁ * a₂)

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
