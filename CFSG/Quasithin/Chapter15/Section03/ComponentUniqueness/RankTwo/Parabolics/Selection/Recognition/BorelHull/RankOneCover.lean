module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Recognition.BorelHull.Cover
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Suzuki

/-!
# Simultaneous normalizer coverage in the rank-one models

In a simple perfect group, the normalizer of a nonidentity two-subgroup R
is proper: otherwise R is the whole group, making it a solvable two-group.
If a Sylow two-subgroup P normalizes R, the concrete rank-one geometry of
F.1.3(1) therefore places N(R) in the proper Borel N(P). This proves coverage
for PSL₂(2^f), PSU₃(2^f), and the Suzuki groups, using the actual model
equivalences and the simplicity and perfectness inherited by the consumer.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, 15.3.41, printed p.1138,
and the first paragraph of the final proof of 15.3.35, p.1139. The rank-one
families come from 1.1.5(3)(a), pp.501–502, and Theorem C and Remark A.2.4,
p.33. The concrete proper-overgroup input is F.1.3(1), p.260.
-/

public section

open Subgroup
open CFSG.Quasithin.ChapterF.Source

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.BorelHull

private theorem rankOne_sylow_facts {K : Type*} [Group K] [Finite K]
    (hmodel : ClassificationModels.IsBenderModel K) (P : Sylow 2 K) :
    RankOneSylowFacts P := by
  cases hmodel with
  | linear f hf h =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
    exact rankOneSylowFacts_of_equiv P e
      (rankOneSylowFacts_psl2 F f (by omega) hF _)
  | unitary f hf h =>
    obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := h
    exact rankOneSylowFacts_of_equiv P e
      (rankOneSylowFacts_psu3 J f (by omega) hF hconj _)
  | suzuki m _ h =>
    obtain ⟨e⟩ := h
    exact rankOneSylowFacts_of_equiv P e (suzuki_rankOneSylowFacts m _)

/-- Every Bender model covers the full normalizers of a Sylow two-subgroup
and any nonidentity two-subgroup that it normalizes in a proper subgroup. -/
theorem rankOne_twoSubgroupNormalizerCover {K : Type*} [Group K] [Finite K]
    [IsSimpleGroup K] [Group.IsPerfect K]
    (hmodel : ClassificationModels.IsBenderModel K) : TwoSubgroupNormalizerCover K := by
  intro P R hR hp hn
  have hproper : normalizer (R : Set K) < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    let : R.Normal := normalizer_eq_top_iff.mp he
    have htop : R = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal R inferInstance).resolve_left hR
    have hK : IsPGroup 2 K := hp.of_equiv
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)
    let : Group.IsNilpotent K := hK.isNilpotent
    exact Group.IsPerfect.not_isSolvable K inferInstance
  have hf := rankOne_sylow_facts hmodel P
  rw [sup_eq_left.mpr (hf.unique_maximal _ hn hproper)]
  exact hf.proper

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.BorelHull
