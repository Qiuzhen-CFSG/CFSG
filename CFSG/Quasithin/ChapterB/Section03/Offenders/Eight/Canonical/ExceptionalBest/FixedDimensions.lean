module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.ExceptionalBest.Lattice
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.Dimensions
/-!
# Fixed dimensions for every exceptional subgroup

For each of the 67 word subgroups, count binary fixed vectors. Quotient
vectors are normalized at coordinate seven and satisfy constant displacement;
this includes fixed quotient vectors without fixed representatives. The
finite-vector-space cardinality formula then gives all four dimensions.
The resulting core and natural weights are at most seven and six.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition B.3.2(2),(5),(6), printed pp. 83–84.
-/

@[expose] public section
open BinaryPermutation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.Offenders.Eight.ExceptionalBest

/-- Full, deleted, core and natural fixed dimensions for the word subgroups. -/
def dims : Fin 67 → ℕ × ℕ × ℕ × ℕ := ![
  (8, 7, 7, 6),
  (6, 5, 5, 4),
  (6, 5, 5, 4),
  (6, 5, 5, 4),
  (7, 6, 6, 5),
  (5, 4, 4, 3),
  (5, 4, 4, 3),
  (5, 4, 4, 3),
  (7, 6, 6, 5),
  (5, 4, 4, 3),
  (5, 4, 4, 3),
  (5, 4, 4, 3),
  (6, 5, 5, 4),
  (4, 4, 4, 4),
  (4, 4, 4, 4),
  (4, 4, 4, 4),
  (5, 4, 4, 3),
  (5, 4, 4, 3),
  (4, 3, 3, 2),
  (5, 4, 4, 3),
  (4, 3, 3, 2),
  (4, 3, 4, 3),
  (3, 3, 3, 3),
  (5, 4, 4, 3),
  (4, 3, 3, 2),
  (5, 4, 4, 3),
  (4, 3, 3, 2),
  (4, 3, 4, 3),
  (3, 3, 3, 3),
  (5, 4, 4, 3),
  (4, 3, 3, 2),
  (5, 4, 4, 3),
  (4, 3, 3, 2),
  (4, 3, 4, 3),
  (3, 3, 3, 3),
  (6, 5, 5, 4),
  (4, 3, 4, 3),
  (4, 3, 4, 3),
  (4, 3, 4, 3),
  (4, 3, 4, 3),
  (4, 3, 4, 3),
  (3, 2, 3, 2),
  (3, 2, 3, 2),
  (4, 3, 4, 3),
  (3, 2, 3, 2),
  (4, 3, 4, 3),
  (3, 2, 3, 2),
  (4, 3, 4, 3),
  (3, 2, 3, 2),
  (3, 2, 3, 2),
  (4, 3, 4, 3),
  (4, 3, 3, 2),
  (4, 3, 3, 2),
  (3, 2, 3, 2),
  (4, 3, 4, 3),
  (3, 2, 3, 2),
  (3, 2, 3, 2),
  (3, 2, 3, 2),
  (4, 3, 4, 3),
  (3, 2, 3, 2),
  (3, 2, 3, 2),
  (3, 2, 3, 2),
  (4, 3, 4, 3),
  (3, 2, 3, 2),
  (3, 2, 3, 2),
  (3, 2, 3, 2),
  (3, 2, 3, 2)]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem table_dimensions (i : Fin 67) :
    HasDimensions (group i) (dims i).1 (dims i).2.1 (dims i).2.2.1 (dims i).2.2.2 := by
  rw [← closure_perms]
  apply dimensions
  all_goals rw [count_bits]
  all_goals revert i; decide +kernel

theorem table_weight_bounds : ∀ i,
    Nat.log 2 (words i).card + (dims i).2.2.1 ≤ 7 ∧
    Nat.log 2 (words i).card + (dims i).2.2.2 ≤ 6 := by decide +kernel

theorem subgroup_weights (B : Subgroup Perm) (hB : B ≤ exceptional 8 (by decide)) :
    weight (coreRepresentation (Fin 8)) B ≤ 7 ∧
    weight (naturalRepresentation (Fin 8)) B ≤ 6 := by
  obtain ⟨i, rfl⟩ := subgroup_eq_group B hB
  simp only [weight, rank, card_group,
    (table_dimensions i).2.2.1, (table_dimensions i).2.2.2]
  exact table_weight_bounds i


end CFSG.Quasithin.ChapterB.Offenders.Eight.ExceptionalBest
