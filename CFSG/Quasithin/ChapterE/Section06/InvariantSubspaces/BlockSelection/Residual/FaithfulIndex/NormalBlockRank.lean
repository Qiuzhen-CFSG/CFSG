module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.FaithfulIndex.Contracts
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.FaithfulIndex.NormalBlockRank.AlternatingThree
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.FaithfulIndex.NormalBlockRank.BinaryModel
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.FaithfulIndex.NormalBlockRank.Retraction

/-!
# Three-rank above a relatively normal chi-zero block

For a normal L₂(2ⁿ) or A₅ block, remove O₂(L) and use the concrete outer
complement fixing a cubic element. For an A₃ block, the actual four-element
module constructs an extension of the canonical core-quotient map. In both
cases the quotient gains one unit of three-rank when lifted to the overgroup.
Thus a three-group quotient in an overgroup of three-rank at most two has
three-rank at most one.

All normality is relative to J. The proof retains the genuine quotient
isomorphisms, allows the source's central two-extensions, and derives the
needed action kernels and splittings. The A₅ model comparison is only on the
core quotient and does not identify its natural module with the L₂(4) module.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), C.1.7--13,
printed pp.123--125; the block list in E.6.7, printed p.246; and the compressed
block/residual inference in the proof of E.6.14, printed p.251 (PDF p.262).
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
open NormalBlockRank
variable {G : Type*} [Group G] [Finite G]

/-- The rank inequality above a normal even-field L₂-block. The argument in
fact applies without restricting the overgroup quotient to be a three-group. -/
theorem normalL2EvenBlock_quotient_rank_add_one_le (J L : Subgroup G)
    (hLJ : L ≤ J) (hn : (L.subgroupOf J).Normal)
    {n : ℕ} (hL : ChapterC.IsL2EvenBlock L n) :
    letI := hn
    primeRank 3 (J ⧸ L.subgroupOf J) + 1 ≤ primeRank 3 J := by
  let := hn
  obtain ⟨_, _, F, _, _, _, hPSL, _⟩ := hL
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hPSL
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  let eL := subgroupOfEquivOfLe hLJ
  let eQ := QuotientGroup.congr (pCore 2 (L.subgroupOf J)) (pCore 2 L) eL
    (pCore_map_iso 2 eL)
  exact rank_add_one_le_of_core_quotient (L.subgroupOf J)
    ((binaryCubicOuterComplement K).congr (eQ.trans e))

/-- The A₅ quotient calculation retains every permitted central two-cover of
the block and uses the actual PSL₂(4) ≃ A₅ isomorphism. -/
theorem normalAlternatingFiveBlock_quotient_rank_add_one_le (J L : Subgroup G)
    (hLJ : L ≤ J) (hn : (L.subgroupOf J).Normal)
    (hL : ChapterC.IsAlternatingBlock L 5) :
    letI := hn
    primeRank 3 (J ⧸ L.subgroupOf J) + 1 ≤ primeRank 3 J := by
  let := hn
  obtain ⟨e⟩ := hL.2.2.quotient_iso
  let eL := subgroupOfEquivOfLe hLJ
  let eQ := QuotientGroup.congr (pCore 2 (L.subgroupOf J)) (pCore 2 L) eL
    (pCore_map_iso 2 eL)
  exact rank_add_one_le_of_core_quotient (L.subgroupOf J)
    (alternatingFiveCubicOuterComplement.congr (eQ.trans e))

/-- Conditional assembly with exactly the remaining A₃ construction exposed.
The nonabelian block cases are discharged by their concrete models. -/
theorem normalChiZeroQuotientRankInput_of_alternatingThreeRetraction
    (ha : AlternatingThreeQuotientRetractionInput G) : NormalChiZeroQuotientRankInput G := by
  intro J L hLJ hn hL hr hq
  let := hn
  rcases hL with ⟨n, hL⟩ | hL | hL
  · have hh := normalL2EvenBlock_quotient_rank_add_one_le J L hLJ hn hL
    omega
  · obtain ⟨r, hrL⟩ := ha J L hLJ hn hL hq
    obtain ⟨e⟩ := hL.2.2.quotient_iso
    let eL := subgroupOfEquivOfLe hLJ
    let eQ := QuotientGroup.congr (pCore 2 (L.subgroupOf J)) (pCore 2 L) eL
      (pCore_map_iso 2 eL)
    have hc : Nat.card ((L.subgroupOf J) ⧸ pCore 2 (L.subgroupOf J)) = 3 := by
      rw [Nat.card_congr (eQ.trans e).toEquiv, nat_card_alternatingGroup]
      norm_num
    have hh := rank_add_one_le_of_core_retraction (L.subgroupOf J) r hrL hc
    omega
  · have hh := normalAlternatingFiveBlock_quotient_rank_add_one_le J L hLJ hn hL
    omega

/-- In three-rank at most two, a three-group quotient above a relatively
normal chi-zero block has three-rank at most one. -/
theorem normalChiZeroQuotientRankInput : NormalChiZeroQuotientRankInput G :=
  normalChiZeroQuotientRankInput_of_alternatingThreeRetraction
    alternatingThreeQuotientRetractionInput

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
