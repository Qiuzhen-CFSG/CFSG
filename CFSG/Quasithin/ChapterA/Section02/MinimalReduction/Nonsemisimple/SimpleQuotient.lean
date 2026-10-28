module
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankReduction
public import Theory.GroupTheory.GeneralizedFitting.LowTwoRank
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Kernel
public import CFSG.KnownSimple.CarrierCatalogue
/-!
# The actual simple quotient in the nonsemisimple source branch

The earlier source action reduction gives two-rank at most two for the
original section's central quotient. That quotient is semisimple, centerless
and nontrivial. The genuine Brauer–Suzuki rank consequence rules out more
than one component, making it nonabelian simple. The original K-group
hypothesis then supplies its full known-simple carrier predicate.

This constructs the precise carrier entering the remaining rank-two model
sieve; no simplicity or quotient-quasithinness premise is assumed.
Source: Aschbacher–Smith A.2.12, printed pp.35–36.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
    [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

theorem CounterexampleToTheoremA.section_centralQuotient_simple_of_not_semisimple
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) : IsSimpleGroup (S ⧸ center S) := by
  let := h.2.2.2.1.isPerfect
  have hnon : Nontrivial S := by
    by_contra hh
    let : Subsingleton S := not_nontrivial_iff_subsingleton.mp hh
    have hs := primeRank_le_card (G := S) p
    have hb := lemma_A_2_14 h ih
    simp only [Nat.card_unique] at hs
    omega
  let := hnon
  let : Nontrivial (S ⧸ center S) := QuotientGroup.nontrivial_iff.mpr (by
    intro hc
    exact Group.IsPerfect.not_isMulCommutative S (center_eq_top_iff.mp hc))
  apply isSimple_of_semisimple_centerless_twoRank_le_two
  · exact componentLayer_eq_top_of_surjective (QuotientGroup.mk' (center S))
      (QuotientGroup.mk'_surjective _) h.2.2.2.1
  · exact Group.IsPerfect.center_quotient_center_eq_bot S
  · exact h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn

theorem CounterexampleToTheoremA.section_quasisimple_of_not_semisimple
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) : IsQuasisimple S :=
  { toIsPerfect := h.2.2.2.1.isPerfect
    simple := h.section_centralQuotient_simple_of_not_semisimple ih hn }

theorem CounterexampleToTheoremA.section_centralQuotient_knownCarrier_of_not_semisimple
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremAOnProperSections KnownSimple.IsKnownSimple G)
    (hn : ¬ IsSemisimple G) : KnownSimple.IsKnownSimpleCarrier (S ⧸ center S) := by
  let := h.section_centralQuotient_simple_of_not_semisimple ih hn
  exact (((h.2.2.1.isKGroup h.2.1).quotient (center S)).mem).2.2

end CFSG.Quasithin.ChapterA.Section02
