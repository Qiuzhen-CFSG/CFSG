module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalQuotients
public import Theory.GroupTheory.CComponent.OddRankNormal
public import Theory.GroupTheory.CComponent.CubicCenterRankNormal
public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank

/-!
# Classical local members normalized by the original Sylow subgroup

The original core center has order one or three. At an odd prime other
than three, distinct conjugates have additive ranks; at three, the cubic
intersection bound gives rank at least three. Either contradicts the
ambient strongly quasithin bound. Thus odd rank two forces normalization.
The symplectic matrix group supplies two independent cubic actors.

This derives S-normality from the original local-family hypotheses; it
adds neither ambient componenthood nor a normalization assumption. The
parabolic-residual consumer is `SymplecticMembership`.
Source: Aschbacher--Smith A.3.8(3), p.46, and 15.1.20(2), pp.1094--1095.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Odd rank at least two forces normalization by the original Sylow subgroup. -/
theorem localFamily_normalizes_of_oddRank (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hr : 2 ≤ primeRank p (K ⧸ pCore 2 K)) : d.S ≤ normalizer (K : Set G) := by
  let := h.elementary
  let J := K ⊔ d.S
  have hJG : J ≤ d.G1 := sup_le hK.1 d.S_le_G1
  have hsq := caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
    ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left))
  have hsqJ : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hJG)).mp (hsq.subgroup (J.subgroupOf d.G1))
  let ec : K.subgroupOf J ≃* K := subgroupOfEquivOfLe le_sup_left
  let eq := QuotientGroup.congr _ _ ec (pCore_map_iso 2 ec)
  let : IsQuasisimple ((K.subgroupOf J) ⧸ pCore 2 (K.subgroupOf J)) :=
    IsQuasisimple.of_mulEquiv eq.symm
  have hc : Nat.card (center ((K.subgroupOf J) ⧸ pCore 2 (K.subgroupOf J))) = 1 ∨
      Nat.card (center ((K.subgroupOf J) ⧸ pCore 2 (K.subgroupOf J))) = 3 := by
    rw [Nat.card_congr (centerCongr eq).toEquiv]
    exact d.localFamily_coreQuotient_center_card hG h hK.1 hq
  have hr' : 2 ≤ primeRank p ((K.subgroupOf J) ⧸ pCore 2 (K.subgroupOf J)) := by
    rwa [primeRank_equiv p eq]
  have hn : (K.subgroupOf J).Normal := by
    by_cases h3 : p = 3
    · subst p
      exact hK.2.1.normal_of_cubic_core_center_threeRank
        (by
          rcases hc with hc | hc
          · exact hc.le.trans (by decide)
          · exact hc.le) hr'
        (hsqJ.stronglyQuasithin 3 Nat.prime_three (by decide))
    · let : Fact p.Prime := ⟨hp⟩
      apply hK.2.1.normal_of_coprime_core_center_primeRank ho _ hr'
        (hsqJ.stronglyQuasithin p hp ho)
      rcases hc with hc | hc
      · rw [hc]; exact Nat.coprime_one_right p
      · rw [hc]
        exact hp.coprime_iff_not_dvd.mpr (fun hd => h3
          ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd))
  exact (show d.S ≤ J from le_sup_right).trans
    ((normal_subgroupOf_iff_le_normalizer (show K ≤ J from le_sup_left)).mp hn)

/-- Every original local member with symplectic-four core quotient is S-normalized. -/
theorem localFamily_symplectic_four_normalizes (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (K ⧸ pCore 2 K) ≃* Theory.SpecificGroups.SymplecticFour.Sp F) :
    d.S ≤ normalizer (K : Set G) := by
  apply d.localFamily_normalizes_of_oddRank hG h hK hq Nat.prime_three (by decide)
  rw [primeRank_equiv 3 e]
  exact Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.symplectic.trans
    (primeRank_subgroup_le 3 _)


end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
