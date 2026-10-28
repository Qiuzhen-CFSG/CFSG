module
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.SimpleQuotient

/-!
# The prime-cyclic branch in the source catalogue sieve

The literal central quotient is a nontrivial perfect group. Thus it cannot
be a prime-cyclic carrier. Perfectness, rather than a two-rank bound alone,
is the source hypothesis excluding this branch.
Source: Aschbacher–Smith A.2.12, printed p.36.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
/-- A nontrivial perfect group is not a prime-cyclic catalogue carrier. -/
theorem no_prime_cyclic_model {Q : Type u} [Group Q] [Nontrivial Q] [Group.IsPerfect Q]
    (hm : KnownSimple.IsPrimeCyclicCarrier Q) : False := by
  obtain ⟨p, _, ⟨a⟩⟩ := hm
  apply Group.IsPerfect.not_isMulCommutative Q
  rw [isMulCommutative_iff]
  intro x y
  apply a.injective
  rw [map_mul, map_mul, mul_comm]
end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}
/-- The original source quotient cannot enter the prime-cyclic branch. -/
theorem CounterexampleToTheoremA.centralQuotient_no_prime_cyclic_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) (hm : KnownSimple.IsPrimeCyclicCarrier (S ⧸ center S)) : False := by
  let := h.section_centralQuotient_simple_of_not_semisimple ih hn
  let := h.2.2.2.1.isPerfect
  exact Nonsemisimple.RankTwoSieve.no_prime_cyclic_model hm
end CFSG.Quasithin.ChapterA.Section02
