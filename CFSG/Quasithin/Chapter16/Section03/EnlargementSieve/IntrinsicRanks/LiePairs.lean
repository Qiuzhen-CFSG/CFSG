module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Contracts
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Geometry
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Rank
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.IntrinsicRanks.Bounds
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.IntrinsicRanks.LiePairs.Covers
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.IntrinsicRanks.LiePairs.RankOneField
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.IntrinsicRanks.LiePairs.UnitaryExclusion
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.GroupTheory.PrimeRankCentralCover
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# Linear-three comparisons in the ordinary Lie-pair sieve

The exact PSL₃(2ⁿ) rank transports along the genuine model equivalence.
For the permitted PSL₃(4) covers, E1–E2 and the earlier I.2.2(3b) lifting
input give the extra rank, including when the contrary involution lies
inside the enlargement. Thus an automorphism bound of two excludes that
case without a numerical premise on the covering group.

The graph-field pair requires care: for L=PSU₃(2ⁿ), Aut(L) has rank n+1,
as also recorded in G.9 on printed p.356. The stronger rank 4n of the
larger PSL₃(2²ⁿ) still gives the contradiction. The printed uniform claim
m₂(Aut(L))=m₂(L) in 16.3.9 is not used for that pair.

The remaining intrinsic automorphism bounds and the symplectic, G₂ and
standard triality calculations are not proved by this module. The bound
parameters below are explicit outstanding model calculations; they must
be discharged before the source sieve is assembled.

Source: Aschbacher–Smith, 16.1.7(3a–d), printed p.1172, and 16.3.9, p.1180.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.LiePairs

/-- Transport the intrinsic calculation, retaining the source field witness. -/
theorem linearThree_rank {M : Type*} [Group M] [Finite M] {n : ℕ}
    (hn : 0 < n) (hM : ClassicalGroup.IsPSL M 3 (2 ^ n)) :
    primeRank 2 M = 2 * n := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := hM
  rw [primeRank_equiv 2 e]
  exact Matrix.PSL3Even.two_rank F hn hc

/-- Perfectness identifies the smaller derived endpoint with its actual
PSL₃ model, including at field order two. -/
theorem linearThree_derived_model {M : Type*} [Group M] {q : ℕ}
    (hM : ClassicalGroup.IsPSL M 3 q) : ClassicalGroup.IsPSL (commutator M) 3 q := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hM
  let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
    Atlas.psl_perfect 3 (by decide)
  let : Group.IsPerfect M :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact ⟨F, hF, hfin, hc, ⟨((MulEquiv.subgroupCongr
    Group.IsPerfect.commutator_eq_top).trans Subgroup.topEquiv).trans e⟩⟩

/-- The smaller field endpoint in 16.1.7(3a) has rank 2n, including n=1. -/
theorem linearThree_derived_rank {M : Type*} [Group M] [Finite M] {n : ℕ}
    (hn : 0 < n) (hM : ClassicalGroup.IsPSL M 3 (2 ^ n)) :
    primeRank 2 (commutator M) = 2 * n :=
  linearThree_rank hn (linearThree_derived_model hM)

/-- The paired type-A₂ field models have exactly doubled rank. Both
quotients and the actual smaller derived-group equivalence are retained. -/
theorem linearThree_field_comparison {K L M : Type*}
    [Group K] [Group L] [Group M] [Finite K] [Finite L] [Finite M]
    {n : ℕ} (hn : 0 < n)
    (hK : ClassicalGroup.IsPSL (K ⧸ center K) 3 (2 ^ (2 * n)))
    (hM : ClassicalGroup.IsPSL M 3 (2 ^ n))
    (eL : (L ⧸ center L) ≃* commutator M) :
    2 ≤ primeRank 2 (L ⧸ center L) ∧
      primeRank 2 (K ⧸ center K) = 2 * primeRank 2 (L ⧸ center L) := by
  have hsmall := (primeRank_equiv 2 eL).trans (linearThree_derived_rank hn hM)
  have hlarge := linearThree_rank (by omega : 0 < 2 * n) hK
  omega

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {z t : G} {L : Subgroup G}

/-- The actual PSL₃(4) quotient has rank four; the covering rank and the
extra rank in K⟨t⟩ are proved from E1–E2 and the source lifting theorem. -/
theorem exclude_pslThreeFour_cover
    (source : PSLThreeFourCoverLifting.{u})
    (he : HasEvenTypeCentralizers G) (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t)
    (hK : IsCentralizerComponent t (enlargement t L))
    (hLie : IsEvenTypeLieComponent (enlargement t L))
    (hmodel : ClassicalGroup.IsPSL
      (enlargement t L ⧸ center (enlargement t L)) 3 4)
    (hAut : primeRank 2 (MulAut L) ≤ 2) : False := by
  let := pslThreeFour_center_elementary he h.involution hK hLie hmodel
  apply exclude_lifted_doubled_rank h hs
    (pslThreeFour_square_lifts source he h.involution hK hLie hmodel)
    (m := 2) (by decide) _ hAut
  exact (linearThree_rank (n := 2) (by decide) hmodel).ge

/-- The larger graph-field model alone exceeds the upper bound n+3.
This uses the valid unitary automorphism estimate n+1, not the printed
uniform bound n. No centerlessness premise is needed for this argument. -/
theorem exclude_linearThree_graphField
    (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t) {n : ℕ} (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPSL (enlargement t L) 3 (2 ^ (2 * n)))
    (hAut : primeRank 2 (MulAut L) ≤ n + 1) : False := by
  have hr := linearThree_rank (by omega : 0 < 2 * n) hmodel
  have hu := rank_le_aut h hs
  omega

/-- The graph case with centerless PSL₃(2ⁿ) uses the rank-one automorphism
calculation for L=PSL₂(2ⁿ). That calculation belongs to the swapped-factor
owner and remains explicit here. -/
theorem exclude_linearThree_graph
    (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t) {n : ℕ} (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPSL
      (enlargement t L ⧸ center (enlargement t L)) 3 (2 ^ n))
    (hZ : center (enlargement t L) = ⊥)
    (hAut : primeRank 2 (MulAut L) ≤ n) : False := by
  have hr := linearThree_rank (by omega : 0 < n) hmodel
  have he := primeRank_equiv 2
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
  apply exclude_centerless_doubled_rank h hs (m := n) (by omega) _ hAut hZ
  omega

/-- Combine the actual permitted-cover reduction with the graph case.
If the same quotient is PSL₃(4), the intrinsic rank calculation forces
n=2, so precisely the rank-two automorphism input is needed. -/
theorem exclude_linearThree_graph_with_permitted_cover
    (source : PSLThreeFourCoverLifting.{u})
    (he : HasEvenTypeCentralizers G) (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t)
    (hK : IsCentralizerComponent t (enlargement t L))
    (hLie : IsEvenTypeLieComponent (enlargement t L))
    {n : ℕ} (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPSL
      (enlargement t L ⧸ center (enlargement t L)) 3 (2 ^ n))
    (hpermitted : center (enlargement t L) = ⊥ ∨
      ClassicalGroup.IsPSL (enlargement t L ⧸ center (enlargement t L)) 3 4)
    (hAut : primeRank 2 (MulAut L) ≤ n) : False := by
  rcases hpermitted with hZ | hfour
  · exact exclude_linearThree_graph h hs hn hmodel hZ hAut
  · have hr := linearThree_rank (by omega : 0 < n) hmodel
    have hr4 := linearThree_rank (n := 2) (by decide) hfour
    apply exclude_pslThreeFour_cover source he h hs hK hLie hfour
    omega

/-- The field pair is excluded after the quotient-model automorphism bound
is supplied. Faithful descent proves the bound for L itself, even for a
perfect central cover, and E1–E2 handle the permitted nonsimple K. -/
theorem exclude_linearThree_field
    (source : PSLThreeFourCoverLifting.{u})
    (he : HasEvenTypeCentralizers G) (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t)
    (hK : IsCentralizerComponent t (enlargement t L))
    (hLie : IsEvenTypeLieComponent (enlargement t L))
    {M : Type*} [Group M] [Finite M] {n : ℕ} (hn : 0 < n)
    (hmodel : ClassicalGroup.IsPSL
      (enlargement t L ⧸ center (enlargement t L)) 3 (2 ^ (2 * n)))
    (hM : ClassicalGroup.IsPSL M 3 (2 ^ n))
    (eL : (L ⧸ center L) ≃* commutator M)
    (hpermitted : center (enlargement t L) = ⊥ ∨
      ClassicalGroup.IsPSL (enlargement t L ⧸ center (enlargement t L)) 3 4)
    (hAutQuotient : primeRank 2 (MulAut (L ⧸ center L)) ≤ 2 * n) : False := by
  let := h.localSetup.component.quasisimple
  have hAut := (automorphism_primeRank_le_quotient_center (E := L) 2).trans hAutQuotient
  have hsmall := (primeRank_equiv 2 eL).trans (linearThree_derived_rank hn hM)
  have hlarge := linearThree_rank (by omega : 0 < 2 * n) hmodel
  rcases hpermitted with hZ | hfour
  · have heq := primeRank_equiv 2
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
    exact exclude_centerless_doubled_rank h hs (m := 2 * n) (by omega)
      (by omega) hAut hZ
  · have hr4 := linearThree_rank (n := 2) (by decide) hfour
    apply exclude_pslThreeFour_cover source he h hs hK hLie hfour
    omega

end CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks.LiePairs
