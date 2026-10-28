module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs
public import CFSG.Quasithin.ChapterB.Section03.Offenders.FixedTests
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd.Representatives
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd.FullClassification.OrbitBound
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd.FullClassification.PairNormalForm
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.Representation.BinaryPermutation.OrbitFixedSpace

/-!
# Full binary permutation modules in degrees five and seven

Every nontrivial elementary abelian subgroup has rank at most its fixed
codimension on the full binary permutation module. Equality holds precisely
for conjugates of the nontrivial disjoint-transposition groups `A_m`.

The orbit bound forces singleton or pair orbits at equality, with each pair
independently swappable. The pair-orbit normal form identifies the subgroup
with a conjugate of `A_m`. Conversely, the representative calculations and
conjugacy transport give elementary structure and the required equality.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, Proposition B.3.2(1),(4), printed pp. 83–84.
-/

public section

namespace CFSG.Quasithin.ChapterB.Offenders.Odd

open BinaryPermutation Representation.BinaryOffender

/-- Every member of case (a) has full fixed codimension equal to its rank. -/
theorem elementary_and_fixedCodim_full_eq_rank_of_caseAFamily
    {n : ℕ} (hn : n = 5 ∨ n = 7) {A : Subgroup (Equiv.Perm (Fin n))}
    (hA : CaseAFamily n A) :
    IsElementaryTwo A ∧ fixedCodim (representation (Fin n)) A = rank A := by
  obtain ⟨m, hm0, hm, g, rfl⟩ := hA
  refine ⟨(isElementaryTwo_disjointTranspositions hn hm0 hm).map_conj g, ?_⟩
  rw [fixedCodim_map_conj, rank_map_conj, fixedCodim_full_disjointTranspositions hn hm,
    rank_disjointTranspositions hn hm]

/-- Equality in the full-module rank bound exhausts the disjoint-transposition family. -/
theorem caseAFamily_of_elementary_and_fixedCodim_full_eq_rank
    {n : ℕ} (hn : n = 5 ∨ n = 7) {A : Subgroup (Equiv.Perm (Fin n))}
    (hA : IsElementaryTwo A)
    (heq : fixedCodim (representation (Fin n)) A = rank A) :
    CaseAFamily n A := by
  obtain ⟨hsmall, hswap⟩ := pair_orbits_of_fixedCodim_full_eq_rank hn A hA heq
  exact caseAFamily_of_pair_orbits hn A hA.1 hsmall hswap

/-- The exhaustive equality cases for the full module in degrees five and seven. -/
theorem elementary_and_fixedCodim_full_eq_rank_iff_caseAFamily
    {n : ℕ} (hn : n = 5 ∨ n = 7) (A : Subgroup (Equiv.Perm (Fin n))) :
    (IsElementaryTwo A ∧ fixedCodim (representation (Fin n)) A = rank A) ↔
      CaseAFamily n A :=
  ⟨fun ⟨hA, heq⟩ => caseAFamily_of_elementary_and_fixedCodim_full_eq_rank hn hA heq,
    elementary_and_fixedCodim_full_eq_rank_of_caseAFamily hn⟩

end CFSG.Quasithin.ChapterB.Offenders.Odd
