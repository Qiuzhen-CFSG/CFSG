module

public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# Pushing up in constrained 2-locals: initial reductions

Aschbacher–Smith, *The Classification of Quasithin Groups*, §C.4,
pp. 151–154 (1 March 2004 manuscript).

The opening reduction of C.4.1 puts the perfect subgroup `M₀` in the
normalizer of `K`, once A.3.8 bounds the number of conjugates by two.
The contradiction in C.4.4 and the subsequent proof of C.4.5 use the fact
that a nontrivial perfect image cannot be contained in a solvable normalizer.
The lemmas here prove these group-theoretic steps with explicit inputs;
the source-specific classification theorems C.4.1 and C.4.8 require the
earlier section results and are not asserted here.
-/

namespace CFSG.Quasithin.ChapterC.Section04

variable {H D : Type*} [Group H] [Group D]

/-- The normalizer step at the start of C.4.1, after the conjugacy bound
from A.3.8 has been converted to a bound on the normalizer index. -/
public theorem perfect_normalizes_of_index_le_two [Finite H]
    (M₀ K : Subgroup H) [Group.IsPerfect M₀]
    (hK : (Subgroup.normalizer (K : Set H)).index ≤ 2) :
    M₀ ≤ Subgroup.normalizer (K : Set H) :=
  Subgroup.le_of_isPerfect_of_index_le_two M₀ (Subgroup.normalizer (K : Set H)) hK

/-- The non-solvability step used in C.4.4–C.4.5. The kernel condition
expresses precisely that the image of `M₀` is nontrivial. -/
public theorem not_isSolvable_of_perfect_image_le (M₀ : Subgroup H)
    [Group.IsPerfect M₀] (f : H →* D) (hM : ¬ M₀ ≤ f.ker)
    (B : Subgroup D) (hle : M₀.map f ≤ B) : ¬ Group.IsSolvable B := by
  intro hB
  exact Subgroup.map_not_le_of_isPerfect_of_isSolvable M₀ f hM B hle

end CFSG.Quasithin.ChapterC.Section04
