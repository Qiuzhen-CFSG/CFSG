module
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.MathieuJankoOne
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.PermutationSporadics
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.JankoThree
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.JankoFourHeld
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.SuzukiSporadic
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.ONan
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.ConwayOne
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.ConwayTwo
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.FischerTwentyTwo
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.FischerTwentyThree
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.LargeSporadicLocals
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.Thompson
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.Lyons
/-!
# The sporadic branch of the actual two-rank sieve

The concrete elementary subgroups and the separately supplied Fi₂₄ rank
certificate exclude every sporadic entry except M₁₁.
Each bound is transported through the literal catalogue isomorphism; no
order or abstract sporadic recognition is assumed.
Source: Aschbacher–Smith A.2.12, printed p.36.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
variable {Q : Type u} [Group Q] [Finite Q] [Nontrivial Q]
/-- Inspect all twenty-six actual carriers; the Fi₂₄ certificate is produced independently. -/
theorem sporadic_model_of_twoRank_le_two (hr : primeRank 2 Q ≤ 2)
    (hfi : 3 ≤ primeRank 2 Sporadic.Fischer.Fi24Prime.Carrier)
    (hm : KnownSimple.IsSporadicCarrier Q) : Nonempty (Q ≃* Sporadic.Mathieu.M11) := by
  obtain ⟨name,⟨a⟩⟩ := hm
  cases name with
  | m11 => exact ⟨a⟩
  | m12 => exact (no_mathieu_janko_one_model hr .m12 (by simp) a).elim
  | m22 => exact (no_mathieu_janko_one_model hr .m22 (by simp) a).elim
  | m23 => exact (no_mathieu_janko_one_model hr .m23 (by simp) a).elim
  | m24 => exact (no_mathieu_janko_one_model hr .m24 (by simp) a).elim
  | j1 => exact (no_mathieu_janko_one_model hr .j1 (by simp) a).elim
  | j2 => exact (no_three_permutation_models hr .j2 (by simp) a).elim
  | mcl => exact (no_three_permutation_models hr .mcl (by simp) a).elim
  | co3 => exact (no_three_permutation_models hr .co3 (by simp) a).elim
  | j4 => exact (no_janko_four_held_model hr .j4 (by simp) a).elim
  | he => exact (no_janko_four_held_model hr .he (by simp) a).elim
  | hs => exact (no_higman_sims_rudvalis_model hr .hs (by simp) a).elim
  | ru => exact (no_higman_sims_rudvalis_model hr .ru (by simp) a).elim
  | hn => exact (no_three_large_sporadic_models hr .hn (by simp) a).elim
  | babyMonster => exact (no_three_large_sporadic_models hr .babyMonster (by simp) a).elim
  | monster => exact (no_three_large_sporadic_models hr .monster (by simp) a).elim
  | j3 => exact (no_janko_three_model hr a).elim
  | suz => exact (no_suzuki_sporadic_model hr a).elim
  | onan => exact (no_onan_model hr a).elim
  | co1 => exact (no_conway_one_model hr a).elim
  | co2 => exact (no_conway_two_model hr a).elim
  | fi22 => exact (no_fischer_twenty_two_model hr a).elim
  | fi23 => exact (no_fischer_twenty_three_model hr a).elim
  | th => exact (no_thompson_model hr a).elim
  | ly => exact (no_lyons_model hr a).elim
  | fi24Prime =>
    let : Finite KnownSimple.SporadicName.fi24Prime.Carrier := Finite.of_equiv Q a.toEquiv
    have hb : 3 ≤ primeRank 2 KnownSimple.SporadicName.fi24Prime.Carrier := hfi
    rw [← Theory.GroupTheory.primeRank_equiv 2 a] at hb
    omega
end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
