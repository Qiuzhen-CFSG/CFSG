module
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.LocalSylow
public import CFSG.Quasithin.Chapter4.Section03.A5.SourceSetup
public import Theory.GroupTheory.PrimeRankResidualCentralizer
/-!
# The original A₅ residual excludes the C.5.6 counterexample

The literal marked quotient L/O₂(L) is A₅, so L has three-rank at most
one. Passing from H to its two-residual preserves three-rank. When that
residual is the same L, the completed local-Sylow C.5.6 obstruction rules
out the original common-normal counterexample. No ambient Sylow premise
or separate model-rank assertion is assumed.

Source: Aschbacher–Smith 4.3.1, printed p.613, using C.5.6(6), pp.157–158.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

theorem threeRank_le_one : primeRank 3 L ≤ 1 := by
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 L) pCore_isPGroup,
    primeRank_congr 3 d.quotient]
  apply (primeRank_le_iff_elementary_card_le (alternatingGroup (Fin 5))).mpr
  intro E hE
  let := hE
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 3 E).exists_card_eq
  have hd := E.card_subgroup_dvd_card
  rw [hn,nat_card_alternatingGroup, Nat.card_fin] at hd
  have hn1 : n ≤ 1 := by
    by_contra h
    have h9 : 3 ^ 2 ∣ Nat.factorial 5 / 2 :=
      (Nat.pow_dvd_pow 3 (by omega : 2 ≤ n)).trans hd
    norm_num at h9
  rw [hn]
  exact Nat.pow_le_pow_right (by decide : 0 < 3) hn1

theorem source_C56_impossible {H M R S : Subgroup G}
    (h : ChapterC.Section05.BlockAnalysis.OriginalHypotheses H M L R S)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (P : Sylow 2 M) (hP : (P : Subgroup M).map M.subtype = S) : False := by
  have hr : primeRank 3 H ≤ 1 := by
    rw [← ResidualCentralizerRank.primeRank_residual (by decide : Nat.Coprime 2 3)]
    have he : (pResidual 2 H) ≃* L :=
      (equivMapOfInjective (pResidual 2 H) H.subtype H.subtype_injective).trans
        (MulEquiv.subgroupCongr h.residual)
    rw [primeRank_congr 3 he]
    exact d.threeRank_le_one
  exact h.false_of_localSylow_threeRank_one hH hr P hP
end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
