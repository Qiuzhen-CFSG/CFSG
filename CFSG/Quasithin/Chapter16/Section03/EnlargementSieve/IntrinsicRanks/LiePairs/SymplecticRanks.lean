module

public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank

/-!
# Intrinsic symplectic ranks for the ordinary Lie pairs

The explicit Sylow and plane-radical calculation transports through each
source model's actual field and projective-group equivalence. Nonbinary
perfectness identifies the smaller derived model without altering its center
quotient. These intrinsic results supply the symplectic rank terms in the
field and odd graph-field pairs; the full automorphism bound is separate.

Source: Aschbacher–Smith, 16.1.7(3a,d), printed p.1172, and 16.3.9, p.1180.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.LiePairs

/-- The source's actual projective symplectic model has two-rank 3n. -/
theorem symplecticFour_rank {M : Type*} [Group M] [Finite M] {n : ℕ}
    (hn : 0 < n) (hM : ClassicalGroup.IsPSp M 2 (2 ^ n)) :
    primeRank 2 M = 3 * n := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := hM
  rw [primeRank_equiv 2 e]
  exact Theory.SpecificGroups.SymplecticFour.EvenTwoRank.projective_rank hc hn

/-- Perfectness identifies the actual smaller derived carrier with its model. -/
theorem symplecticFour_derived_model {M : Type*} [Group M] {n : ℕ}
    (hn : 2 ≤ n) (hM : ClassicalGroup.IsPSp M 2 (2 ^ n)) :
    ClassicalGroup.IsPSp (commutator M) 2 (2 ^ n) := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hM
  let := Theory.SpecificGroups.SymplecticFour.EvenTwoRank.projective_perfect hc hn
  let : Group.IsPerfect M :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact ⟨F, hF, hfin, hc, ⟨((MulEquiv.subgroupCongr
    Group.IsPerfect.commutator_eq_top).trans Subgroup.topEquiv).trans e⟩⟩

/-- The genuine derived endpoint has two-rank 3n for every source field witness. -/
theorem symplecticFour_derived_rank {M : Type*} [Group M] [Finite M] {n : ℕ}
    (hn : 2 ≤ n) (hM : ClassicalGroup.IsPSp M 2 (2 ^ n)) :
    primeRank 2 (commutator M) = 3 * n :=
  symplecticFour_rank (by omega) (symplecticFour_derived_model hn hM)

end CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.LiePairs
