module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.SylowCenters
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Separation of source rank-one Sylow subgroups

The actual rank-one model gives the unique proper Sylow-overgroup property.
Involutions are central in their Sylow subgroups. In a group with trivial
two-core, a common involution therefore forces two Sylow subgroups to agree:
its centralizer is proper, so lies in one Sylow normalizer and contains both
Sylows. Pullback through O₂ gives the same test for an elementary subgroup
escaping the local core. Small Suzuki and unitary parameters and the D₁₀
source exception are retained.

Source: DGS, *Groups and Graphs* (1985), 5.1(c,d), pp.104--105,
and the generation step of 8.1(g), p.133. The local generation consumer
uses this on the actual quotient of the terminal local group.
-/

@[expose] public noncomputable section
open Subgroup Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial

private theorem central_involution_eq_one {D : Type*} [Group D]
    (hcore : pCore 2 D = ⊥) {x : D} (hx : x ^ 2 = 1) (hz : x ∈ center D) : x = 1 := by
  have hc : zpowers x ≤ center D := zpowers_le.mpr hz
  have hn : (zpowers x).Normal := ⟨by
    intro y hy g
    have he := mem_center_iff.mp (hc hy) g
    simpa only [he, mul_inv_cancel_right] using hy⟩
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one hx)
  have hle : zpowers x ≤ pCore 2 D := le_sSup ⟨hn, hp⟩
  exact mem_bot.mp (hcore ▸ hle (mem_zpowers x))

/-- A nontrivial involution determines its Sylow subgroup in the actual
core-free source rank-one quotient. This supplies the part of 5.1(c)
needed for the elementary Chapter 8 moving span. -/
theorem source_rank_one_sylow_eq_of_common_involution
    {D : Type*} [Group D] [Finite D] (M : IsRankOneModel D)
    (hcore : pCore 2 D = ⊥) (S T : Sylow 2 D)
    (x : D) (hxS : x ∈ S) (hxT : x ∈ T) (hx1 : x ≠ 1) (hx2 : x ^ 2 = 1) : S = T := by
  have hcentral (R : Sylow 2 D) (hxR : x ∈ R) :
      (R : Subgroup D) ≤ centralizer ({x} : Set D) := by
    have hz := source_rank_one_sylow_square_central M R ⟨x, hxR⟩ (Subtype.ext hx2)
    intro r hr
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨r, hr⟩)
  have hc : centralizer ({x} : Set D) < ⊤ := lt_top_iff_ne_top.mpr (by
    intro he
    apply hx1
    apply central_involution_eq_one hcore hx2
    apply mem_center_iff.mpr
    intro y
    exact mem_centralizer_singleton_iff.mp (he ▸ mem_top y))
  have hn := (M.rankOneSylowFacts S).unique_maximal _ (hcentral S hxS) hc
  have hTS : (T : Subgroup D) ≤ S := by
    have hi := T.isPGroup'.inf_normalizer_sylow S
    rw [inf_eq_left.mpr ((hcentral T hxT).trans hn)] at hi
    exact inf_eq_left.mp hi.symm
  exact Sylow.ext (T.is_maximal' S.isPGroup' hTS)

/-- In a local group, a shared elementary subgroup escaping O₂ forces
its two containing Sylow subgroups to coincide, through the same quotient. -/
theorem local_sylow_eq_of_elementary_escape
    {L : Type*} [Group L] [Finite L]
    (M : IsRankOneModel (L ⧸ pCore 2 L))
    (S T : Sylow 2 L) (A : Subgroup L) [IsElementaryAbelian 2 A]
    (hAS : A ≤ S) (hAT : A ≤ T) (he : ¬ A ≤ pCore 2 L) : S = T := by
  obtain ⟨x, hxA, hxQ⟩ := Set.not_subset.mp he
  let q := QuotientGroup.mk' (pCore 2 L)
  let S' := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
  let T' := T.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 L))
  have hx1 : q x ≠ 1 := by
    intro hx
    exact hxQ ((QuotientGroup.eq_one_iff x).mp hx)
  have hx2 : (q x) ^ 2 = 1 := by
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (p := 2) x hxA, map_one]
  have heq := source_rank_one_sylow_eq_of_common_involution M
    (pCore_quotient_pCore_eq_bot 2) S' T' (q x)
    (mem_map_of_mem q (hAS hxA)) (mem_map_of_mem q (hAT hxA)) hx1 hx2
  apply Sylow.ext
  have hh := congrArg (fun R : Sylow 2 (L ⧸ pCore 2 L) => (R : Subgroup _).comap q) heq
  change ((S : Subgroup L).map q).comap q = ((T : Subgroup L).map q).comap q at hh
  simpa only [comap_map_eq, q, QuotientGroup.ker_mk',
    sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal S),
    sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal T)] using hh

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
