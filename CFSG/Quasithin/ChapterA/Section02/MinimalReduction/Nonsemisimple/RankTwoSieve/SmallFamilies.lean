module

public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankReduction
public import Theory.SpecificGroups.Alternating.TwoRankSieve
public import Theory.SpecificGroups.G2.TwoRankLower
public import Theory.SpecificGroups.Suzuki.TwoRank
public import Theory.SpecificGroups.Triality.StandardTwoRank

/-!
# Concrete family exclusions in the two-rank-two source branch

The regular elementary eight excludes Aₙ for n ≥ 8. Torus/Weyl or root
coordinates exclude every full G₂ carrier; the exact Suzuki rank excludes
every simple-range Suzuki carrier. The cubic root subgroup excludes every
binary triality carrier. Each bound is transported through the literal model
isomorphism, and the final applications use the proved rank bound on the
original source quotient S/Z(S).

These are branches of the full known-simple catalogue, not a replacement
for its remaining classical, exceptional, small-derived and sporadic cases.
Source: Aschbacher–Smith A.2.12, printed p.36.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
variable {Q : Type u} [Group Q] [Finite Q]

/-- An alternating carrier of two-rank at most two has degree at most seven. -/
theorem alternating_degree_le_seven (hr : primeRank 2 Q ≤ 2) {n : ℕ}
    (a : Q ≃* alternatingGroup (Fin n)) : n ≤ 7 := by
  by_contra hn
  have hb := alternatingGroup.TwoRankSieve.three_le_primeRank (by omega : 8 ≤ n)
  rw [← primeRank_equiv 2 a] at hb
  omega

/-- The entire full-octonion G₂ entry of the catalogue is excluded. -/
theorem not_g2_carrier (hr : primeRank 2 Q ≤ 2) :
    ¬ KnownSimple.IsG2Carrier Q := by
  rintro ⟨F, hF, hfin, _, ⟨a⟩⟩
  have hb := Atlas.G2.three_le_primeRank_two F
  rw [← primeRank_equiv 2 a] at hb
  omega

/-- Every simple-range Suzuki matrix carrier has two-rank at least three. -/
theorem no_suzuki_model (hr : primeRank 2 Q ≤ 2) (m : ℕ) (hm : 1 ≤ m)
    (a : Q ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : False := by
  rw [primeRank_equiv 2 a,
    BenderSuzuki.MatrixGroups.suzuki_two_rank m (by omega)] at hr
  omega

/-- The cubic root subgroup excludes every binary triality model. -/
theorem no_binary_triality_model (hr : primeRank 2 Q ≤ 2) (n : ℕ) (hn : 0 < n)
    (hmodel : Triality.Standard.IsTrialityGroupAt (2 ^ n) Q) : False := by
  have hlow := Triality.Standard.TwoRank.derived_twoRank_ge_three_mul_of_model n hn hmodel
  have hle := _root_.primeRank_le_of_injective 2 (commutator Q).subtype Subtype.val_injective
  omega

end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

/-- The actual source quotient can only be alternating in degrees five to seven. -/
theorem CounterexampleToTheoremA.centralQuotient_alternating_degree_le_seven
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) {n : ℕ}
    (a : (S ⧸ center S) ≃* alternatingGroup (Fin n)) : n ≤ 7 :=
  Nonsemisimple.RankTwoSieve.alternating_degree_le_seven
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) a

/-- The full G₂ catalogue branch is impossible for the literal quotient S/Z(S). -/
theorem CounterexampleToTheoremA.centralQuotient_not_g2_carrier
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) : ¬ KnownSimple.IsG2Carrier (S ⧸ center S) :=
  Nonsemisimple.RankTwoSieve.not_g2_carrier
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn)

/-- The Suzuki catalogue branch is impossible for the literal quotient S/Z(S). -/
theorem CounterexampleToTheoremA.centralQuotient_no_suzuki_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) (m : ℕ) (hm : 1 ≤ m)
    (a : (S ⧸ center S) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : False :=
  Nonsemisimple.RankTwoSieve.no_suzuki_model
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) m hm a

/-- The binary triality catalogue branch is impossible for the source quotient. -/
theorem CounterexampleToTheoremA.centralQuotient_no_binary_triality_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) (n : ℕ) (hn0 : 0 < n)
    (hmodel : Triality.Standard.IsTrialityGroupAt (2 ^ n) (S ⧸ center S)) : False :=
  Nonsemisimple.RankTwoSieve.no_binary_triality_model
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) n hn0 hmodel

end CFSG.Quasithin.ChapterA.Section02
