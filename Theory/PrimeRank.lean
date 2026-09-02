module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Rank

/-!
# Prime rank and group rank

For a finite group, the `p`-rank can equivalently be computed as the largest
generator rank of an abelian `p`-subgroup or as the largest rank of an
elementary abelian `p`-subgroup. The former description is used here because
it is the established interface in the Feit--Thompson development.
-/

@[expose] public section

open scoped IsMulCommutative

/-- The `q`-rank of a finite group: the maximal generator rank of an abelian
`q`-subgroup. -/
noncomputable def primeRank (q : ℕ) (G : Type*) [Group G] : ℕ :=
  sSup
    {n : ℕ |
      ∃ A : Subgroup G,
        IsPGroup q A
        ∧ IsMulCommutative A
        ∧ ∃ hA : Group.FG A, n ≤ @Group.rank A inferInstance hA
    }

/-- The rank of a finite group: the maximal `q`-rank over primes `q`. -/
noncomputable def groupRank (G : Type*) [Group G] : ℕ :=
  sSup {n : ℕ | ∃ q : ℕ, q.Prime ∧ n ≤ primeRank q G}
