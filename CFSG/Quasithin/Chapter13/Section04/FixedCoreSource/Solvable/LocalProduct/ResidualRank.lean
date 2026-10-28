module

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.SingleFactor
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.Noncentrality
public import Theory.GroupTheory.SymmetricThreeActorRank
public import Theory.Quasithin.CoprimeRank

/-!
# Three-rank of the original first centralizer residual

In the two-core-kernel case, the actual L₁ image is two-perfect and
normalizes the marked Sylow subgroup of the normal Thompson S₃ factor.
It therefore centralizes that factor, leaving three-rank at most one.
The action kernel is a two-group, so it preserves three-rank; the cubic
divisor of |L₁| supplies the reverse bound.

The Baumann application constructs R₁ as the stated action-core preimage
and discharges Thompson noncentrality. SourceProduct uses this rank-one
conclusion together with the literal local product. Source placement,
residual order, A₆-block noncentrality and the larger-kernel branch remain
with qt-d-1341-solvable-source. This does not yet select L/O₂(L)≅A₆.
Source: Aschbacher–Smith 13.4.8, printed pp.904–905.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Stellmacher Chapter14.Section03.FaithfulSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem centralizer_firstResidual_threeRank_of_twoCore_kernel
    (h₀ : Hypothesis1331 T L) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (R : Subgroup G) (hRT : R ≤ T)
    (hnR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hQR : (centralizer ({z} : Set G)).pCoreIn 2 ≤ R)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z} : Set G)))
    (hkernel : centralizer ((centralizerOmegaOrbit T z).subgroupOf
      (centralizer ({z} : Set G)) : Set (centralizer ({z} : Set G))) =
      pCore 2 (centralizer ({z} : Set G)))
    (horder : ∃ m n : ℕ, Nat.card (firstCentralizerResidual L z) ∣ 2 ^ m * 3 ^ n)
    (hthree : 3 ∣ Nat.card (firstCentralizerResidual L z))
    (hAN : firstCentralizerResidual L z ≤ normalizer (R : Set G)) :
    primeRank 3 (firstCentralizerResidual L z) = 1 := by
  let H := centralizer ({z} : Set G)
  let U := (centralizerOmegaOrbit T z).subgroupOf H
  let := (centralizerOmegaOrbit_reduced h₀ hz hz1).normal
  let q := QuotientGroup.mk' (centralizer (U : Set H))
  let N := conjugateSpanBy (elementaryAbelianMaxJ R) H
  let I := (N.subgroupOf H).map q
  let J := ((elementaryAbelianMaxJ R).subgroupOf H).map q
  let A := firstCentralizerResidual L z
  let B := (A.subgroupOf H).map q
  have hAH : A ≤ H := (firstCentralizerResidual_le L z).trans inf_le_right
  have hpA := firstCentralizerResidual_twoPerfect L z
  have hpAi : IsPPerfect 2 (A.subgroupOf H) := hpA.of_surjective
    (subgroupOfEquivOfLe hAH).symm.toMonoidHom (subgroupOfEquivOfLe hAH).symm.surjective
  have hpB : IsPPerfect 2 B := hpAi.of_surjective (q.subgroupMap (A.subgroupOf H))
    (q.subgroupMap_surjective _)
  have hJH : elementaryAbelianMaxJ R ≤ H :=
    (sSup_le fun _ hB => hB.1).trans (hRT.trans (original_sylow_le_centralizer hz))
  have hNH : N ≤ H := conjugateSpanBy_le_self hJH
  let : (N.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNH).mpr (le_normalizer_conjugateSpanBy _ _)
  let : I.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  obtain ⟨e⟩ := centralizer_thompson_single_factor_of_twoCore_kernel h₀ hz hz1 R hRT hnR hQR hJ
    hsolv hkernel A hAH hpA horder hAN
    (firstCentralizerResidual_noncentral_of_twoCore_kernel hkernel hthree)
  obtain ⟨P,hP⟩ := centralizer_thompson_span_sylow h₀ hz hz1 R hRT hnR hQR hJ hsolv
  have hnB : B ≤ normalizer (J : Set _) := by
    have hAi : A.subgroupOf H ≤ normalizer ((elementaryAbelianMaxJ R).subgroupOf H : Set H) := by
      rw [← subgroupOf_normalizer_eq hJH]
      exact subgroupOf_mono H (hAN.trans (normalizer_le_normalizer_elementaryAbelianMaxJ R))
    exact (map_mono hAi).trans (((elementaryAbelianMaxJ R).subgroupOf H).le_normalizer_map q)
  have hrank : primeRank 3 H ≤ 2 :=
    (isQuasithin_iff_twoLocal.mp h₀.qtke.quasithin) H
      (isTwoLocal_involution_centralizer
        (orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.1 hz1))
      3 (by decide) (by decide)
  have hqrank : primeRank 3 (H ⧸ centralizer (U : Set H)) ≤ 2 := by
    rw [primeRank_congr 3 (QuotientGroup.quotientMulEquivOfEq hkernel)]
    exact (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans hrank
  have hBrank : primeRank 3 B ≤ 1 :=
    NormalSymmetricThree.threeRank_le_one_of_twoPerfect_normalizer I e P B hpB
      (hP.symm ▸ hnB) hqrank
  let f := q.subgroupMap (A.subgroupOf H)
  have hk : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk', hkernel]
    exact pCore_isPGroup.comap_subtype
  have hAiRank : primeRank 3 (A.subgroupOf H) ≤ 1 := by
    apply (primeRank_le_of_coprime_ker 3 f ?_).trans hBrank
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hArank : primeRank 3 A ≤ 1 := by
    rwa [primeRank_congr 3 (subgroupOfEquivOfLe hAH)] at hAiRank
  have hne : primeRank 3 A ≠ 0 := fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he hthree
  change primeRank 3 A = 1
  omega
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Stellmacher Chapter14.Section03.FaithfulSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem centralizer_firstResidual_threeRank_of_baumann_bound
    (h₀ : Hypothesis1331 T L) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    {K : Type*} [Group K] (f : T →* K) (R : Subgroup G)
    (hR : R = ((pCore 2 K).comap f).map (T : Subgroup G).subtype)
    (hQR : (centralizer ({z} : Set G)).pCoreIn 2 ≤ R)
    (hsolv : Group.IsSolvable (centralizer ({z} : Set G)))
    (hkernel : centralizer ((centralizerOmegaOrbit T z).subgroupOf
      (centralizer ({z} : Set G)) : Set (centralizer ({z} : Set G))) =
      pCore 2 (centralizer ({z} : Set G)))
    (hB : normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G))
    (hout : ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (horder : ∃ m n : ℕ, Nat.card (firstCentralizerResidual L z) ∣ 2 ^ m * 3 ^ n)
    (hthree : 3 ∣ Nat.card (firstCentralizerResidual L z))
    (hAN : firstCentralizerResidual L z ≤ normalizer (R : Set G)) :
    primeRank 3 (firstCentralizerResidual L z) = 1 := by
  have hRT : R ≤ T := by
    rw [hR]
    exact map_subtype_le _
  have hnR : (T : Subgroup G) ≤ normalizer (R : Set G) := by
    rw [hR]
    have hh := (map_mono (show (⊤ : Subgroup T) ≤ normalizer ((pCore 2 K).comap f : Set T)
      from le_normalizer_of_normal)).trans
        (((pCore 2 K).comap f).le_normalizer_map (T : Subgroup G).subtype)
    simpa only [← MonoidHom.range_eq_map,range_subtype] using hh
  let H := centralizer ({z} : Set G)
  let U := (centralizerOmegaOrbit T z).subgroupOf H
  have hRH : R ≤ H := hRT.trans (original_sylow_le_centralizer hz)
  have hcore : R ⊓ centralizer (centralizerOmegaOrbit T z : Set G) = H.pCoreIn 2 := by
    apply le_antisymm
    · intro a ha
      have hc : (⟨a,hRH ha.1⟩ : H) ∈ centralizer (U : Set H) := by
        intro v hv
        exact Subtype.ext (ha.2 v.val hv)
      exact mem_map_of_mem H.subtype (hkernel ▸ hc)
    · intro a ha
      refine ⟨hQR ha, ?_⟩
      obtain ⟨b,hb,rfl⟩ := ha
      have hc : b ∈ centralizer (U : Set H) := hkernel.symm ▸ hb
      intro v hv
      exact congrArg Subtype.val (hc ⟨v,centralizerOmegaOrbit_le hz hv⟩ hv)
  have hJ := centralizer_thompson_noncentral_of_baumann_bound h₀ hz hz1 R hRT hcore hB hout
  exact centralizer_firstResidual_threeRank_of_twoCore_kernel h₀ hz hz1 R hRT hnR hQR hJ
    hsolv hkernel horder hthree hAN
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
