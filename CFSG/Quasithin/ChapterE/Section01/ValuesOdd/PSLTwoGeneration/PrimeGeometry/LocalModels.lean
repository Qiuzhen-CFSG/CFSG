module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.LargeFamily
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.FieldReduction
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Perm.Basic

/-!
# Concrete local subgroups for the prime-field calculation

The proposed local witnesses are symmetric groups of degree four with a
nonnormal actor four-group, and dihedral groups of order four times an odd
prime. The actor's position is part of the S₄ condition: the normal four-group
has trivial image modulo O₂(S₄), so it cannot serve as an E1 actor.

`ConcreteLocalGeometryAt` records the remaining placement calculation, using
actual subgroup isomorphisms and the literal Sylow intersection. It asserts
neither the intrinsic E1 conditions nor their existence in a linear model.
Those are separate proof obligations, assembled in `Reduction`.

Source: Aschbacher--Smith, E.1.2 and E.1.14(6), pp.210 and 214,
and the cited Aschbacher (1982), Lemma 4.10.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- The two concrete solvable local shapes, retaining the actor's position. -/
def LocalModel (A H : Subgroup G) : Prop :=
  (Nonempty (H ≃* Equiv.Perm (Fin 4)) ∧ ¬ (A.subgroupOf H).Normal) ∨
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ Nonempty (H ≃* DihedralGroup (2 * r))

/-- The remaining model geometry, before verifying the intrinsic E1 quotient. -/
def ConcreteLocalGeometryAt (T : Sylow 2 G) : Prop :=
  ∀ Ω : Set (Subgroup G), IsElementaryFamily Ω →
    (∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ → 1 < Group.rank A) →
    ∀ M : Subgroup G, IsCoatom M → (T : Subgroup G) ≤ M →
      normalizer (weakClosure (T : Subgroup G) Ω : Set G) ≤ M →
      ∃ A : Subgroup G, A ∈ Ω ∧ A ≤ (T : Subgroup G) ∧ IsKleinFour A ∧
        ∃ H : Subgroup G, A ≤ H ∧
          (∃ S : Sylow 2 H, (S : Subgroup H) = (T : Subgroup G).subgroupOf H) ∧
          LocalModel A H ∧ ¬ H ≤ M

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry
