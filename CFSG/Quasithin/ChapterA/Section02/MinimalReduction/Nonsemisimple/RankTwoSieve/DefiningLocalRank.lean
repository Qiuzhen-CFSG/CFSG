module

public import Theory.SpecificGroups.Classical.DefiningLocalRank.SignedThree
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.SignedThree

/-!
# The defining signed-three branch of the nonsemisimple source reduction

The actual PSL₃ and PSU₃ models have defining-prime two-local rank at most
max(2,e). Consequently the source failure m₂,p>2 forces e>2. The proper
SL₂ subgroup in the original quotient then contradicts induction on the
original group's proper sections. No quasithinness of the quotient is assumed.

Source: Aschbacher–Smith A.2.12, printed p.36. The earlier prime-core reduction
and the production of the local-rank failure retain their original owners.
-/

public section
open Subgroup Theory.GroupTheory Matrix
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
variable {Q : Type u} [Group Q] [Finite Q]

/-- Transport the proved defining local rank bound to an actual PSL₃ model. -/
theorem isPSL_three_defining_twoLocalPrimeRank_le
    (p e : ℕ) (hp : p.Prime) (ho : Odd p) (he : 0 < e)
    (hmodel : ClassicalGroup.IsPSL Q 3 (p ^ e)) :
    twoLocalPrimeRank p Q ≤ max 2 e := by
  obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := hmodel
  let : Fact p.Prime := ⟨hp⟩
  rw [twoLocalPrimeRank_mulEquiv p a]
  exact Theory.SpecificGroups.DefiningLocalRank.psl3_twoLocalPrimeRank_le_max ho he hcard

/-- The unitary transport preserves the stored field, form and Frobenius action. -/
theorem isPSU_three_defining_twoLocalPrimeRank_le
    (p e : ℕ) (hp : p.Prime) (ho : Odd p) (he : 0 < e)
    (hmodel : ClassicalGroup.IsPSU Q 3 (p ^ e)) :
    twoLocalPrimeRank p Q ≤ max 2 e := by
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨a⟩⟩ := hmodel
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective a a.surjective
  let : Fact p.Prime := ⟨hp⟩
  rw [twoLocalPrimeRank_mulEquiv p a]
  exact Theory.SpecificGroups.DefiningLocalRank.psu3_twoLocalPrimeRank_le_max
    J ho he hcard hconj

variable {K : GroupClass.{u}} {G : Type u} [Group G] [Finite G]

/-- Actual defining local-rank failure supplies the large exponent needed by
the proper-SL₂ induction contradiction in the linear branch. -/
theorem no_psl_three_quotient_of_defining_local_rank_gt_two
    (ih : TheoremsOnProperSections K G) (hqt : IsQuasithin G) (hk : IsKGroup K G)
    (f : G →* Q) (hf : Function.Surjective f)
    (p e : ℕ) (hp : p.Prime) (ho : Odd p) (he : 0 < e)
    (hmodel : ClassicalGroup.IsPSL Q 3 (p ^ e))
    (hrank : 2 < twoLocalPrimeRank p Q) : False := by
  have hb := isPSL_three_defining_twoLocalPrimeRank_le p e hp ho he hmodel
  have he2 : 2 < e := by omega
  exact no_psl_three_large_quotient ih hqt hk f hf p e hp ho he2 hmodel

/-- The same original-source contradiction for the unitary branch. -/
theorem no_psu_three_quotient_of_defining_local_rank_gt_two
    (ih : TheoremsOnProperSections K G) (hqt : IsQuasithin G) (hk : IsKGroup K G)
    (f : G →* Q) (hf : Function.Surjective f)
    (p e : ℕ) (hp : p.Prime) (ho : Odd p) (he : 0 < e)
    (hmodel : ClassicalGroup.IsPSU Q 3 (p ^ e))
    (hrank : 2 < twoLocalPrimeRank p Q) : False := by
  have hb := isPSU_three_defining_twoLocalPrimeRank_le p e hp ho he hmodel
  have he2 : 2 < e := by omega
  exact no_psu_three_large_quotient ih hqt hk f hf p e hp ho he2 hmodel

end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
end
