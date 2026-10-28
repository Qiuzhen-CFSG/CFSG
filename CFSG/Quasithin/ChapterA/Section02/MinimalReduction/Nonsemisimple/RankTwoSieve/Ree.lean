module

public import CFSG.KnownSimple.ExceptionalModels
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.BinaryEndpoints
public import Theory.SpecificGroups.ReeG2.TwoRankLower
public import Theory.SpecificGroups.ReeG2.TernaryDerivedEquiv.B2ProjectiveComparison
public import Theory.SpecificGroups.ReeG2.TernaryDerivedEquiv.MatrixHom

/-!
# Excluding the full and small-derived Ree G₂ entries

The full Ree matrix carrier contains an elementary eight. Its small derived
endpoint is literally PSL₂(8), by the checked projective permutation and
seven-dimensional matrix comparisons; the root subgroup again has rank three.
Both contradictions are applied to the original source quotient S/Z(S).
Source: Aschbacher–Smith A.2.12, printed p.36; GLS III §2.2 for the small alias.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
variable {Q : Type u} [Group Q] [Finite Q]

/-- No full Ree G₂ catalogue model has two-rank at most two. -/
theorem no_reeG2_model (hr : primeRank 2 Q ≤ 2) {q : ℕ}
    (hmodel : ExceptionalGroup.IsReeG2 Q q) : False := by
  obtain ⟨m, F, hF, hfin, hchar, _, _, ⟨a⟩⟩ := hmodel
  have hb := Atlas.ReeG2.three_le_twoRank F m
  rw [← primeRank_equiv 2 a] at hb
  omega

/-- The actual small Ree commutator has the rank-three binary PSL₂ root subgroup. -/
theorem no_smallRee_model (hr : primeRank 2 Q ≤ 2)
    (a : Q ≃* commutator (Atlas.ReeG2.Model (ZMod 3) 0)) : False := by
  let e := Atlas.ReeG2.TernaryDerived.equivOfPermutationModel
    Atlas.ReeG2.TernaryDerived.b2ProjectiveEquiv
    Atlas.ReeG2.TernaryDerived.toRee Atlas.ReeG2.TernaryDerived.toRee_ne_one
  have hm : ClassicalGroup.IsPSL Q 2 (2 ^ 3) :=
    ⟨GaloisField 2 3, inferInstance, inferInstance, GaloisField.card 2 3 (by decide),
      ⟨a.trans e⟩⟩
  have := psl_two_binary_exponent_le_two hr hm
  omega

end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

/-- The full Ree G₂ branch is impossible for the literal source quotient. -/
theorem CounterexampleToTheoremA.centralQuotient_no_reeG2_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) {q : ℕ}
    (hmodel : ExceptionalGroup.IsReeG2 (S ⧸ center S) q) : False :=
  Nonsemisimple.RankTwoSieve.no_reeG2_model
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) hmodel

/-- The separate small Ree commutator is impossible for the literal source quotient. -/
theorem CounterexampleToTheoremA.centralQuotient_no_smallRee_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G)
    (a : (S ⧸ center S) ≃* commutator (Atlas.ReeG2.Model (ZMod 3) 0)) : False :=
  Nonsemisimple.RankTwoSieve.no_smallRee_model
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) a

end CFSG.Quasithin.ChapterA.Section02
