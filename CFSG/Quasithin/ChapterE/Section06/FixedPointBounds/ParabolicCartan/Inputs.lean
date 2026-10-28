module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.Contracts
public import CFSG.Quasithin.ChapterB.Section06To07.Structure
public import Theory.GroupTheory.Hall.Basic

/-!
# Inputs and construction output for the E.6.27 Cartan branch

`Source4413One` is the generation clause of 4.4.13(1), retaining the
simple QTKE ambient group (and hence proper-K), the nontrivial two-core,
the genuine Sylow and unique maximal subgroup, and the Hall, elementary
abelian and permutation hypotheses. An injective embedding retains the
original parabolic type, so n(H) is never silently transferred to a
new carrier. This is an earlier-source proposition, not its proof.

`HallCartanData` is instead an intermediate construction target. Its witness
is the complete E.3.37 witness in the literal C_M(U). Its Hall subgroup and
Frattini factorization must be constructed from the marked E.2.2 models;
they are not earlier-source assumptions. In particular this record asserts
neither faithfulness nor any normalizer escape.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), printed
pp.239, 257 and 623--624. The family H in 4.4.13 is defined by O₂(H) ≠ 1
in the introduction to Volume II.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan

open Subgroup ChapterB
open scoped Pointwise

universe u
variable {G X : Type u} [Group G] [Finite G] [Group X] [Finite X]

/-- The odd primes, for a literal Hall 2'-subgroup. -/
def oddPrimes : Set Nat.Primes := {p | p.val ≠ 2}

/-- The exact generation conclusion of 4.4.13(1), specialized to a minimal
parabolic. The embedding places H in the original simple QTKE group.
No arbitrary odd subgroup may be substituted for the elementary A. -/
def Source4413One (Kc : GroupClass.{u}) (G : Type u) [Group G] [Finite G] : Prop :=
  IsSimpleQTKE Kc G →
  ∀ (X : Type u) (_ : Group X) (_ : Finite X) (f : X →* G),
    Function.Injective f → pCore 2 X ≠ ⊥ → 1 < generationParameter X →
    ∀ (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (Y : Subgroup X),
      Y ≤ minimalParabolicMax S hP →
      IsHallSubgroup oddPrimes (Y.subgroupOf (minimalParabolicMax S hP)) →
      ∀ (p : ℕ), p.Prime → ∀ A : Subgroup X,
        IsElementaryAbelian p A → A ≤ Y →
        (A : Set X) * (S : Set X) = (S : Set X) * (A : Set X) →
        minimalParabolicMax S hP ⊔ normalizer (A : Set X) = ⊤

/-- Intrinsic marked-model construction target. Every field is an output to
be proved, not an earlier-source oracle. Solvability of the unique maximal
subgroup is retained for its separate placement argument. -/
structure IntrinsicHallCartanData (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) (n : ℕ) where
  witness : NPrimeWitness X n
  sylow_eq : witness.sylow = S
  hall_le : witness.abelianGroup ≤ minimalParabolicMax S hP
  hall : IsHallSubgroup oddPrimes
    (witness.abelianGroup.subgroupOf (minimalParabolicMax S hP))
  maximal_solvable : Group.IsSolvable (minimalParabolicMax S hP)
  twoGroup : Subgroup X
  normalizes : witness.abelianGroup ≤ normalizer (twoGroup : Set X)
  frattini : (S : Set X) = (twoGroup : Set X) *
    ((S : Subgroup X) ⊓ normalizer (witness.abelianGroup : Set X) : Set X)

/-- Output to be constructed from E.2.2, not a substitute for that theorem.
The subgroup Y lives in the original parabolic and maps to the full odd
abelian overgroup in the published n' witness. -/
structure HallCartanData (f : X →* G) (M U : Subgroup G)
    (S : Sylow 2 X) (n : ℕ) where
  witness : NPrimeWitness ↥(M ⊓ centralizer (U : Set G)) n
  hallGroup : Subgroup X
  twoGroup : Subgroup X
  hall_image : hallGroup.map f =
    witness.abelianGroup.map (M ⊓ centralizer (U : Set G)).subtype
  sylow_image : (S : Subgroup X).map f =
    (witness.sylow : Subgroup ↥(M ⊓ centralizer (U : Set G))).map
      (M ⊓ centralizer (U : Set G)).subtype
  hall_le : hallGroup ≤ M.comap f
  hall : IsHallSubgroup oddPrimes (hallGroup.subgroupOf (M.comap f))
  normalizes : hallGroup ≤ normalizer (twoGroup : Set X)
  frattini : (S : Set X) = (twoGroup : Set X) *
    ((S : Subgroup X) ⊓ normalizer (hallGroup : Set X) : Set X)

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan

end
