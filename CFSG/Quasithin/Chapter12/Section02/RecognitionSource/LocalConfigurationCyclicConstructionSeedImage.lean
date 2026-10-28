module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionSeedSupplement
public import CFSG.Quasithin.ChapterI.Section06To08.PairElementary.OddQuotient

/-!
# The order-two image before invariant odd-subgroup selection

The prescribed-Sylow hyperplane pair has both mutual normalizers in O₂(H),
by its abelian image modulo the normal odd core. Movement of V excludes
index one, so its literal image in H/O₂(H) has order two. This derives the
quotient conclusion of 12.2.21 without assuming CyclicConstructionSeed.

The initial pair-core recognition, invariant-Sylow selection, noncyclic
exclusion and final cyclic-block assembly remain with qt-d-12213-cyclic-block.
Source: Aschbacher–Smith, 12.2.21, printed p.802.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H : Subgroup G} {d p : ℕ} {P : Subgroup G}

/-- The hyperplane of the actual prescribed-Sylow pair lies in O₂(H).
This proves the order-two image before selecting the inverter-invariant Sylow. -/
theorem CyclicOddSupplement.quotient_module_card_two
    (S : CyclicOddSupplement T L p H P) (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V) :
    Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2 := by
  let := D.elementary
  have hVH : V ≤ H := D.le_sylow.trans S.hstar.1.1.2
  have hPH : P ≤ H := S.overgroup ▸ le_sup_left
  let E := V.subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hVH
  have hETI : IsTISubgroup E := by
    apply (isTISubgroup_iff E).mpr
    intro g hg x hx hgx
    apply Subtype.ext
    apply (isTISubgroup_iff V).mp hTI g ?_ x hx hgx
    intro hn
    exact hg (V.le_normalizer_comap H.subtype hn)
  obtain ⟨g, hg, _, _, hi⟩ := S.exists_hyperplane_pair D A hT hTI
  let a : H := ⟨g, hPH hg⟩
  let B := V.map (MulAut.conj g).toMonoidHom
  have hBH : B ≤ H := by
    rintro x ⟨v, hv, rfl⟩
    exact H.mul_mem (H.mul_mem (hPH hg) (hVH hv)) (H.inv_mem (hPH hg))
  have heB : E.map (MulAut.conj a).toMonoidHom = B.subgroupOf H := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom hv
    · rintro ⟨v, hv, hve⟩
      exact ⟨⟨v, hVH hv⟩, hv, Subtype.ext hve⟩
  have hiE : (normalizer (E.map (MulAut.conj a).toMonoidHom : Set H)).relIndex E = 2 := by
    rw [heB, ← subgroupOf_normalizer_eq hBH, relIndex_subgroupOf hVH]
    exact hi
  have haR : q a ∈ pCore p (H ⧸ pCore 2 H) := by
    rw [← S.quotient_core]
    exact mem_map_of_mem q hg
  have hY := ti_pair_mutual_normalizers_le_kernel_of_odd_image E hETI q
    (pCore p (H ⧸ pCore 2 H)) pCore_isPGroup (Nat.coprime_two_left.mpr S.odd_prime)
    a haR hiE
  have hU : E ⊓ normalizer (E.map (MulAut.conj a).toMonoidHom : Set H) ≤ q.ker :=
    le_sup_left.trans hY
  have hd : q.ker.relIndex E ∣ 2 := by
    have hh := relIndex_dvd_of_le_left E hU
    rwa [inf_relIndex_left, hiE] at hh
  have hneq : q.ker.relIndex E ≠ 1 := by
    intro he
    have hk := relIndex_eq_one.mp he
    apply A.hstar_movement H S.hstar
    intro x hx
    exact mem_map_of_mem H.subtype
      (show (⟨x, hVH hx⟩ : H) ∈ pCore 2 H from by
        simpa only [q, QuotientGroup.ker_mk'] using
          hk (show (⟨x, hVH hx⟩ : H) ∈ E from hx))
  rw [← relIndex_ker]
  exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left hneq

/-- Source 12.2.21's literal quotient image has order two under the original
natural analysis. No pair-core or invariant-selection record is assumed. -/
theorem chosen_hstar_quotient_module_card_two (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2 := by
  obtain ⟨p, P, S⟩ := chosen_hstar_exists_odd_supplement D A hH
  exact S.quotient_module_card_two D A hT hTI

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
