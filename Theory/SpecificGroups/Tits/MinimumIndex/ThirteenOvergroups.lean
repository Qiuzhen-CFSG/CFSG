module

public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.Seeds
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.CandidateRigidity
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration
public import Theory.SpecificGroups.Tits.Atlas1600Order
public import Theory.GroupTheory.PrimeCyclicCoverage
import Mathlib.Tactic.FinCases

/-!
# Coverage of proper Tits subgroups with order divisible by thirteen

Cauchy's theorem and Sylow conjugacy normalize a subgroup with order divisible
by thirteen so that it contains the marked cyclic subgroup `⟨ab⟩`. Such a
subgroup either normalizes `⟨ab⟩`, or contains two distinct conjugates of it.
The latter case reduces to generation of a conjugate candidate derived subgroup
and rigidity of its proper overgroups. Conjugation is composed in the actual
Atlas carrier, with the literal shared candidates as the final output.

The final `coverage` theorem discharges generation, rigidity and normalizer
placement using the independently checked certificates. It supplies precisely
the thirteen-coverage premise of the minimum-index assembly. The conditional
reductions remain available with their existing interfaces.

Source: the primary ATLAS Tits entry and programs preserved in
`MinimumIndex/source/`; `Seeds` gives the exact conventions. Coverage is proved
on the actual carrier rather than assumed from the maximal-subgroup catalogue.
-/

namespace Tits.MinimumIndexThirteen
open Subgroup

private theorem conjugate_ne_top (L : Subgroup Atlas1600Group) (hL : L ≠ ⊤)
    (g : Atlas1600Group) : L.map (MulAut.conj g).toMonoidHom ≠ ⊤ := by
  intro he
  apply hL
  apply Subgroup.index_eq_one.mp
  rw [← Subgroup.index_map_of_bijective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).bijective L, he, Subgroup.index_top]

/-- Cauchy and Sylow conjugacy put the marked thirteen-subgroup in a conjugate
of every proper subgroup whose order is divisible by thirteen. -/
public theorem exists_conjugate_contains_thirteenSubgroup (L : Subgroup Atlas1600Group)
    (hL : L ≠ ⊤) (h13 : 13 ∣ Nat.card L) :
    ∃ g : Atlas1600Group, L.map (MulAut.conj g).toMonoidHom ≠ ⊤ ∧
      thirteenSubgroup ≤ L.map (MulAut.conj g).toMonoidHom := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 13 h13
  have hx' : orderOf (x : Atlas1600Group) = 13 := by
    rwa [Subgroup.orderOf_coe]
  obtain ⟨k, g, hg⟩ := PrimeCyclicCoverage.exists_conjugate_pow_of_prime_sq_not_dvd
    (by decide : Nat.Prime 13)
    (by rw [atlas1600Group_card]; decide : ¬ 13 ^ 2 ∣ Nat.card Atlas1600Group)
    hx' generator_order
  refine ⟨g, conjugate_ne_top L hL g, ?_⟩
  apply Subgroup.zpowers_le.mpr
  rw [hg]
  exact Subgroup.mem_map_of_mem _ (L.pow_mem x.property k)

private theorem pair_le {L : Subgroup Atlas1600Group} (hP : thirteenSubgroup ≤ L)
    {x : Atlas1600Group} (hx : x ∈ L) : pairSubgroup x ≤ L := by
  apply sup_le hP
  rintro y ⟨z, hz, rfl⟩
  exact L.mul_mem (L.mul_mem hx (hP hz)) (L.inv_mem hx)

/-- Pair generation and candidate rigidity give normalized overgroup coverage.
All three certificate premises remain explicit. -/
public theorem normalized_coverage_of_generation_and_rigidity
    (hgenerate : ∀ x : Atlas1600Group, x ∉ thirteenNormalizer →
      ∃ (i : Fin 3) (g : Atlas1600Group),
        candidateDerived i ≤ (pairSubgroup x).map (MulAut.conj g).toMonoidHom)
    (hrigid : ∀ (i : Fin 3) (L : Subgroup Atlas1600Group), L ≠ ⊤ →
      candidateDerived i ≤ L → L ≤ candidate i)
    (hnormalizer : ∃ g : Atlas1600Group,
      thirteenNormalizer.map (MulAut.conj g).toMonoidHom ≤ MinimumIndexCandidates.max1)
    (L : Subgroup Atlas1600Group) (hL : L ≠ ⊤) (hP : thirteenSubgroup ≤ L) :
    ∃ (g : Atlas1600Group) (i : Fin 3),
      L.map (MulAut.conj g).toMonoidHom ≤ candidate i := by
  classical
  by_cases hN : L ≤ thirteenNormalizer
  · obtain ⟨g, hg⟩ := hnormalizer
    exact ⟨g, 0, (Subgroup.map_mono hN).trans hg⟩
  · obtain ⟨x, hx, hxN⟩ := SetLike.not_le_iff_exists.mp hN
    obtain ⟨i, g, hi⟩ := hgenerate x hxN
    exact ⟨g, i, hrigid i _ (conjugate_ne_top L hL g)
      (hi.trans (Subgroup.map_mono (pair_le hP hx)))⟩

private theorem map_conj_map_conj (L : Subgroup Atlas1600Group) (g h : Atlas1600Group) :
    (L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      L.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

/-- The three explicit certificate inputs produce precisely the thirteen-coverage
input of `atlas1600_subgroup_index_ge_of_candidate_coverage`. The order bounds
and other prime branches are independent; this is a conditional reduction. -/
public theorem coverage_of_generation_and_rigidity
    (hgenerate : ∀ x : Atlas1600Group, x ∉ thirteenNormalizer →
      ∃ (i : Fin 3) (g : Atlas1600Group),
        candidateDerived i ≤ (pairSubgroup x).map (MulAut.conj g).toMonoidHom)
    (hrigid : ∀ (i : Fin 3) (L : Subgroup Atlas1600Group), L ≠ ⊤ →
      candidateDerived i ≤ L → L ≤ candidate i)
    (hnormalizer : ∃ g : Atlas1600Group,
      thirteenNormalizer.map (MulAut.conj g).toMonoidHom ≤ MinimumIndexCandidates.max1)
    (L : Subgroup Atlas1600Group) (hL : L ≠ ⊤) (h13 : 13 ∣ Nat.card L) :
    ∃ g : Atlas1600Group,
      L.map (MulAut.conj g).toMonoidHom ≤ MinimumIndexCandidates.max1 ∨
      L.map (MulAut.conj g).toMonoidHom ≤ MinimumIndexCandidates.max2 ∨
      L.map (MulAut.conj g).toMonoidHom ≤ MinimumIndexCandidates.max4 := by
  obtain ⟨g, hg, hP⟩ := exists_conjugate_contains_thirteenSubgroup L hL h13
  obtain ⟨h, i, hi⟩ := normalized_coverage_of_generation_and_rigidity
    hgenerate hrigid hnormalizer _ hg hP
  rw [map_conj_map_conj] at hi
  refine ⟨h * g, ?_⟩
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr hi)

/-- Every proper subgroup of the actual Tits carrier whose order is divisible
by thirteen is conjugate into the literal ATLAS max1, max2 or max4 candidate.
This discharges `hthirteen` in
`atlas1600_subgroup_index_ge_of_candidate_coverage`, with all generation,
rigidity and normalizer-placement premises proved on the same carrier. -/
public theorem coverage (L : Subgroup Atlas1600Group) (hL : L ≠ ⊤)
    (h13 : 13 ∣ Nat.card L) :
    ∃ g : Atlas1600Group,
      L.map (MulAut.conj g).toMonoidHom ≤ MinimumIndexCandidates.max1 ∨
      L.map (MulAut.conj g).toMonoidHom ≤ MinimumIndexCandidates.max2 ∨
      L.map (MulAut.conj g).toMonoidHom ≤ MinimumIndexCandidates.max4 :=
  coverage_of_generation_and_rigidity pair_generation candidateDerived_rigid
    thirteenNormalizer_conjugate_le_max1 L hL h13

end Tits.MinimumIndexThirteen
