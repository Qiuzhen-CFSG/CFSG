module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeLocal
public import CFSG.Quasithin.Chapter3.Section01.CommonNormalKnownSimple
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.GroupTheory.SylowNormalizedSupIndex

/-!
# A zero-core prime actor cannot normalize the original S

Set S = O₂(N_G(L) ∩ H) and K = O²(H), with both embedded in G.
The source equality S ∩ K = T ∩ K makes S Sylow in KS. If an actor D
normalized S, then DT would have nontrivial two-core containing S.
The original common-normal theorem 3.1.1 applied to DT and H would
produce a nontrivial normal two-subgroup of DH, contradicting O₂(DH)=1.

The application to the literal prime local pair establishes that S is
not relatively normal in DS. It does not assume that D normalizes the
chosen rank-one factor, and it does not require O₂(G₀)=1.

Source: Aschbacher--Smith, proof of original 5.2.2, printed p.647,
`refs/quasithin.pdf`. This is the nonnormality step before the small
left quotient and F.1.1 model exclusions.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The residual Sylow intersection makes the literal S Sylow in KS. -/
theorem residual_join_sourceS_sylow {T : Sylow 2 G} {L H : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H)
    (hSK : Global.sourceS L H ⊓ residual H = (T : Subgroup G) ⊓ residual H) :
    Chapter1.IsSylowIn 2 (Global.sourceS L H) (residual H ⊔ Global.sourceS L H) := by
  have hST := Global.sourceS_le_sylow hTL hTH
  obtain ⟨P, hP⟩ := NormalSylowQuotientAction.intersection_sylow T (residual H)
    (hTH.trans (le_normalizer_residual H))
  have hPS : (P : Subgroup (residual H)).map (residual H).subtype ≤ Global.sourceS L H := by
    rw [hP, subgroupOf_map_subtype, ← hSK]
    exact inf_le_left
  exact (T.isPGroup'.to_le hST).exists_sylow_sup_of_coprime_index
    (residual H) (Global.sourceS L H) (hST.trans (hTH.trans (le_normalizer_residual H)))
    (P : Subgroup (residual H)) P.not_dvd_index hPS

/-- The original common-normal theorem rules out normalization of S by a
zero-core actor, before any rank-two amalgam is classified. -/
theorem zero_core_not_normalizes_sourceS {T : Sylow 2 G} {L W H D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hSK : Global.sourceS L H ⊓ residual H = (T : Subgroup G) ⊓ residual H)
    (hz : (D ⊔ H).pCoreIn 2 = ⊥) :
    ¬ D ≤ normalizer (Global.sourceS L H : Set G) := by
  intro hDN
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hST := Global.sourceS_le_sylow h.sylow_normalizes hTH
  have hcore : H.pCoreIn 2 ≤ Global.sourceS L H :=
    Chapter3.twoCore_le_of_sylow_le T (le_inf h.sylow_normalizes hTH)
      (show Global.intersection L H ≤ H from inf_le_right)
  have hS : Global.sourceS L H ≠ ⊥ :=
    fun he => hH.1.1.1 (bot_unique (he ▸ hcore))
  have hTS : (T : Subgroup G) ≤ normalizer (Global.sourceS L H : Set G) :=
    (le_inf h.sylow_normalizes hTH).trans (Global.intersection_normalizes_sourceS L H)
  have hnorm : D ⊔ (T : Subgroup G) ≤ normalizer (Global.sourceS L H : Set G) :=
    sup_le hDN hTS
  have hSDT : Global.sourceS L H ≤ D ⊔ (T : Subgroup G) := hST.trans le_sup_right
  have hcDT : Global.sourceS L H ≤ (D ⊔ (T : Subgroup G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le hST) hSDT hnorm
  have hDT : D ⊔ (T : Subgroup G) ∈ Chapter1.HOver G (T : Set G) :=
    ⟨fun he => hS (bot_unique (he ▸ hcDT)), fun _ hx => mem_sup_right hx⟩
  obtain ⟨N, hNS, hN, hn⟩ := Chapter3.source_common_normal_knownSimple h.qtke T
    (D ⊔ (T : Subgroup G)) H (Global.sourceS L H) hDT hH.1.1
    (Chapter3.HStar.hasUniqueMaximalOver T h.sylow_normalizes hH) hS hST
    (residual_join_sourceS_sylow h.sylow_normalizes hTH hSK) hnorm
  have hgen : Chapter3.generated (D ⊔ (T : Subgroup G)) H = D ⊔ H := by
    rw [Chapter3.generated_eq_sup, sup_assoc, sup_eq_right.mpr hTH]
  have hn' : D ⊔ H ≤ normalizer (N : Set G) := by
    simpa only [hgen] using (Chapter3.normalIn_iff_le_normalizer.mp hn).2
  have hNC := le_pCoreIn_of_normalizes (T.isPGroup'.to_le (hNS.trans hST))
    (hNS.trans (hST.trans (hTH.trans le_sup_right))) hn'
  exact hN (bot_unique (hz ▸ hNC))

/-- Apply the common-normal contradiction to the actual chosen pair. -/
theorem LocalData.prime_actor_not_normalizes_sourceS
    {T : Sylow 2 G} {L W H A B D L₂ : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D L₂) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hd : CartanPrimeActor A H p D) :
    ¬ D ≤ normalizer (Global.sourceS L H : Set G) :=
  zero_core_not_normalizes_sourceS h hH d.S_intersection_residual hd.zero_core

/-- Source 5.2.2 uses relative, rather than ambient, nonnormality in DS. -/
theorem LocalData.sourceS_not_normal_in_left
    {T : Sylow 2 G} {L W H A B D L₂ : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D L₂) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hd : CartanPrimeActor A H p D) :
    ¬ ((Global.sourceS L H).subgroupOf (D ⊔ Global.sourceS L H)).Normal := by
  intro hn
  have hn' := (normal_subgroupOf_iff_le_normalizer
    (show Global.sourceS L H ≤ D ⊔ Global.sourceS L H from le_sup_right)).mp hn
  exact d.prime_actor_not_normalizes_sourceS h hH hd (le_sup_left.trans hn')

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
