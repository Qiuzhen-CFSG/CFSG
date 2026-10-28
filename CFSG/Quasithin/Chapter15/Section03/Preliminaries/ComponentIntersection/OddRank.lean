module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.OddRank.Intersection
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.OddRank.QuotientOrder
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.OddRank.CoreNormalization

/-!
# Odd-rank deductions for 15.3.12

The imported proofs establish that `Y_L = O²(Y₊ ∩ L)` is nontrivial from
`m₃(Y₊) = 2`, `m₃(L) ≥ 1`, the ambient SQTK rank bound, and the earlier
component orbit and theta identities. If `m₃(L) = 1`, the genuine
three-group and exponent properties of `Y₊/O₂(Y₊)` give
`|Y_L/O₂(Y_L)| = 3` and `|Y_L|₃ = 3`.

The commutator `[Y_L,R]` is contained in the local two-core `R`. The
component-permutation argument then makes `R` normalize `L`, using the
actual nonnormal models of 1.2.1(3). We assemble this with nontriviality
and the core-product containment, discharging the normalization proof's
nontriviality input. The same Chapter 1 alternative supplies the orbit
bound, so no independent index hypothesis is needed.

These are conditional local deductions: the source assembly supplies the
Sylow and theta conclusions of 15.3.11, the SQTK rank bound, the structural
conclusions of 1.2.1(2)–(3), and the stated properties of the genuine quotient
`Y₊/O₂(Y₊)`. The inner-action splitting in 15.3.12(2) belongs to the parent
assembly and is not asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 15.3.12, printed pp.1124–1125 (PDF pp.1141–1142).
-/

public section

open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.Chapter15.Section03.ComponentIntersection

open CFSG.Quasithin.Chapter1.Section02

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normalizer_relIndex_le_two_of_relative_alternative
    {I L : Subgroup G} (hLI : L ≤ I)
    (h : (L.subgroupOf I).Normal ∨
      (normalizer (L.subgroupOf I : Set I)).index = 2) :
    (normalizer (L : Set G)).relIndex I ≤ 2 := by
  change ((normalizer (L : Set G)).subgroupOf I).index ≤ 2
  rw [subgroupOf_normalizer_eq hLI]
  rcases h with hn | hi
  · let := hn
    rw [normalizer_eq_top, index_top]
    decide
  · exact hi.le

/-- All three conclusions of 15.3.12(1), conditional on the displayed earlier
local and component facts. In particular, neither nontriviality of the
intersection residual nor normalization by the local core is an input. -/
theorem odd_rank_component_intersection_of_local_facts
    {Y S M I L : Subgroup G}
    (hI : I ∈ outsideFamily Y S M) (hSM : S ≤ M)
    (htheta : theta (M ⊓ I) = Y)
    (hLI : L ≤ I) (hL : (L.subgroupOf I).IsCComponent)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hcomm : ∀ K : Subgroup I, K.IsCComponent → K ≠ L.subgroupOf I →
      ⁅L.subgroupOf I, K⁆ ≤ (L.subgroupOf I).pCoreIn 2 ⊓ K.pCoreIn 2 ∧
        (L.subgroupOf I).pCoreIn 2 ⊓ K.pCoreIn 2 ≤ pCore 2 I)
    (hstructure : (L.subgroupOf I).Normal ∨
      (normalizer (L.subgroupOf I : Set I)).index = 2 ∧
        NonnormalCComponentModel ((L.subgroupOf I) ⧸ pCore 2 (L.subgroupOf I)))
    (hYrank : primeRank 3 Y = 2) (hLrank : 1 ≤ primeRank 3 L)
    (hr : primeRank 3 I ≤ 2) :
    intersectionResidual Y L ≠ ⊥ ∧
      localCore Y S ≤ normalizer (L : Set G) ∧
      (L.pCoreIn 2 : Set G) * ((intersectionResidual Y L).pCoreIn 2 : Set G) ⊆
        (localCore Y S : Set G) := by
  have hindex := normalizer_relIndex_le_two_of_relative_alternative hLI
    (hstructure.imp_right And.left)
  obtain ⟨hne, hcores⟩ := intersection_ne_bot_and_core_product_le
    hI hSM htheta hLI hL P hP hindex hYrank hLrank hr
  exact ⟨hne, localCore_le_normalizer_of_component_facts
    hI hLI hL hcomm hstructure hne, hcores⟩

/-- The rank-one specialization adds the actual intersection quotient's order
and the three-part of the intersection residual. Its exponent input concerns
`Y/O₂(Y)`, as supplied by 15.3.11(5), and does not assert that `Y` has exponent three. -/
theorem rank_one_component_intersection_of_local_facts
    {Y S M I L : Subgroup G}
    (hI : I ∈ outsideFamily Y S M) (hSM : S ≤ M)
    (htheta : theta (M ⊓ I) = Y)
    (hLI : L ≤ I) (hL : (L.subgroupOf I).IsCComponent)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hcomm : ∀ K : Subgroup I, K.IsCComponent → K ≠ L.subgroupOf I →
      ⁅L.subgroupOf I, K⁆ ≤ (L.subgroupOf I).pCoreIn 2 ⊓ K.pCoreIn 2 ∧
        (L.subgroupOf I).pCoreIn 2 ⊓ K.pCoreIn 2 ≤ pCore 2 I)
    (hstructure : (L.subgroupOf I).Normal ∨
      (normalizer (L.subgroupOf I : Set I)).index = 2 ∧
        NonnormalCComponentModel ((L.subgroupOf I) ⧸ pCore 2 (L.subgroupOf I)))
    (hYrank : primeRank 3 Y = 2) (hLrank : primeRank 3 L = 1)
    (hr : primeRank 3 I ≤ 2)
    (hq : IsPGroup 3 (TwoCoreQuotient Y))
    (he : Monoid.exponent (TwoCoreQuotient Y) ∣ 3) :
    intersectionResidual Y L ≠ ⊥ ∧
      localCore Y S ≤ normalizer (L : Set G) ∧
      (L.pCoreIn 2 : Set G) * ((intersectionResidual Y L).pCoreIn 2 : Set G) ⊆
        (localCore Y S : Set G) ∧
      Nat.card (TwoCoreQuotient (intersectionResidual Y L)) = 3 ∧
      3 ^ (Nat.card (intersectionResidual Y L)).factorization 3 = 3 := by
  obtain ⟨hne, hnorm, hcores⟩ := odd_rank_component_intersection_of_local_facts
    hI hSM htheta hLI hL P hP hcomm hstructure hYrank hLrank.ge hr
  have hindex := normalizer_relIndex_le_two_of_relative_alternative hLI
    (hstructure.imp_right And.left)
  have hcard := intersectionResidual_quotient_card_eq_three_of_local_facts
    hI htheta hLI hindex hYrank hLrank hr hq he
  exact ⟨hne, hnorm, hcores, hcard, three_part_eq_three_of_quotient_card hcard⟩

end CFSG.Quasithin.Chapter15.Section03.ComponentIntersection
