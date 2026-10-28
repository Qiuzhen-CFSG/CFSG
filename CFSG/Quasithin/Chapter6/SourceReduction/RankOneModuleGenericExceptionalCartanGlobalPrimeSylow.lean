module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeConstruction
public import Theory.GroupTheory.PResidual.ConjugateSpanNormalizer
public import Theory.GroupTheory.SylowIndexTwoOvergroup
public import Mathlib.GroupTheory.IndexNormal
public import Theory.GroupTheory.ConjugateOrbitIndexTwo
/-!
# Movement and changed Sylow subgroups in original 5.2.2

In the nonzero-core branch put T₀=N_T(L₂). The zero-core actor forces
T₀<T, hence its source index bound is an equality. Since S≤T₀ and T
normalizes DS, it also normalizes DT₀. The residual is exactly the span
of the T-conjugates of L₂. Thus an actor fixing L₂ would fix the residual,
contradicting the original choice of D. The two-coset formula also gives
the literal pair of conjugates generating that residual.

A Sylow subgroup of G₀T₀B containing T₀ has index at most two over T₀;
if it is larger, it is an ambient Sylow subgroup. Finally source 3.1.1
constructs a nonzero core for ⟨N_G(T₀),H⟩, the overgroup used by the
subsequent component embedding argument.

The right-factor construction, zero-core exclusions, and the component
classification giving the cubic plane remain with the consolidated owner
qt-d-1222-rankone-cartan-local-to-global. This module does not assert the
full normalization conclusion. Source: Aschbacher--Smith, 5.2.2, p.648.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The selected source factor and T generate the literal residual orbit span. -/
theorem LocalData.residual_eq_conjugateSpan
    {T : Sylow 2 G} {L H B D L₂ : Subgroup G}
    (d : LocalData T L H B D L₂) :
    residual H = conjugateSpanBy L₂ (T : Subgroup G) :=
  embedded_pResidual_eq_conjugateSpanBy L₂ (T : Subgroup G) H
    d.right_le_residual T.isPGroup' d.right_generate

/-- In the nonzero-core branch the relative normalizer has index exactly two. -/
theorem LocalData.normalizingSylow_index
    {T : Sylow 2 G} {L H A B D L₂ : Subgroup G} {p : ℕ}
    (d : LocalData T L H B D L₂) (hTH : (T : Subgroup G) ≤ H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D L₂).pCoreIn 2 ≠ ⊥) :
    (normalizingSylow T L₂).relIndex (T : Subgroup G) = 2 := by
  have hn := (d.normalizingSylow_lt hTH c hd hz).not_ge
  have hi : (normalizingSylow T L₂).relIndex (T : Subgroup G) ≠ 1 :=
    fun he => hn (relIndex_eq_one.mp he)
  have hp := ((normalizingSylow T L₂).subgroupOf (T : Subgroup G)).index_ne_zero_of_finite
  change (normalizingSylow T L₂).relIndex (T : Subgroup G) ≠ 0 at hp
  have hb := d.index_le_two
  omega

/-- The original S lies in the literal normalizer T₀. -/
theorem LocalData.sourceS_le_normalizingSylow
    {T : Sylow 2 G} {L W H B D L₂ : Subgroup G} {n : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D L₂) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    Global.sourceS L H ≤ normalizingSylow T L₂ :=
  le_inf (Global.sourceS_le_sylow h.sylow_normalizes hH.1.1.2) d.S_normalizes_right

/-- Index two and normalization of DS give normalization of DT₀ by T. -/
theorem LocalData.sylow_normalizes_actor_join
    {T : Sylow 2 G} {L W H A B D L₂ : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D L₂) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D L₂).pCoreIn 2 ≠ ⊥) :
    (T : Subgroup G) ≤ normalizer ((D ⊔ normalizingSylow T L₂ : Subgroup G) : Set G) := by
  let T₀ := normalizingSylow T L₂
  have hS := d.sourceS_le_normalizingSylow h hH
  have he : (D ⊔ Global.sourceS L H) ⊔ T₀ = D ⊔ T₀ := by
    rw [sup_assoc, sup_eq_right.mpr hS]
  have hn : (T₀.subgroupOf (T : Subgroup G)).Normal :=
    normal_of_index_eq_two (d.normalizingSylow_index hH.1.1.2 c hd hz)
  have hn' := (normal_subgroupOf_iff_le_normalizer
    (show T₀ ≤ (T : Subgroup G) from inf_le_left)).mp hn
  rw [← he]
  exact (le_inf (le_sup_left.trans d.TB_normalizes_left) hn').trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- A prime actor moving the residual must move the selected right factor. -/
theorem LocalData.prime_actor_not_normalizes_right
    {T : Sylow 2 G} {L W H A B D L₂ : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D L₂) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D L₂).pCoreIn 2 ≠ ⊥) :
    ¬ D ≤ normalizer (L₂ : Set G) := by
  intro hD
  apply h.prime_actor_not_normalizes hH hd
  rw [d.residual_eq_conjugateSpan]
  exact le_sup_left.trans (normalizes_conjugateSpanBy_of_normalized_actor
    L₂ (T : Subgroup G) (D ⊔ normalizingSylow T L₂)
    (sup_le hD inf_le_right) (d.sylow_normalizes_actor_join h hH c hd hz))

/-- Construct the local Sylow over T₀ and certify when it is ambient Sylow. -/
theorem LocalData.exists_changedSylow
    {T : Sylow 2 G} {L H A B D L₂ : Subgroup G} {p : ℕ}
    (d : LocalData T L H B D L₂) (hTH : (T : Subgroup G) ≤ H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D L₂).pCoreIn 2 ≠ ⊥) :
    ∃ P : Sylow 2 (extension T L H B D L₂),
      let T₁ := (P : Subgroup (extension T L H B D L₂)).map
        (extension T L H B D L₂).subtype
      normalizingSylow T L₂ ≤ T₁ ∧
      (normalizingSylow T L₂).relIndex T₁ ≤ 2 ∧
      (T₁ = normalizingSylow T L₂ ∨ ∃ U : Sylow 2 G, (U : Subgroup G) = T₁) := by
  let E := extension T L H B D L₂
  let T₀ := normalizingSylow T L₂
  have hTE : T₀ ≤ E := le_sup_right.trans le_sup_left
  have hp : IsPGroup 2 (T₀.subgroupOf E) :=
    (T.isPGroup'.to_le (show T₀ ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  have hPT : T₀ ≤ (P : Subgroup E).map E.subtype := by
    simpa only [map_subgroupOf_eq_of_le hTE] using map_mono (f := E.subtype) hP
  refine ⟨P,hPT,?_⟩
  exact two_group_over_index_two_sylow T T₀ _ inf_le_left
    (d.normalizingSylow_index hTH c hd hz) (P.isPGroup'.map E.subtype) hPT

/-- The source residual intersection makes T₀ Sylow in KT₀. -/
theorem LocalData.normalizingSylow_sylow_in_residual_join
    {T : Sylow 2 G} {L W H B D L₂ : Subgroup G} {n : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D L₂) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    Chapter1.IsSylowIn 2 (normalizingSylow T L₂)
      (residual H ⊔ normalizingSylow T L₂) := by
  obtain ⟨P, hP⟩ := NormalSylowQuotientAction.intersection_sylow T (residual H)
    (hH.1.1.2.trans (le_normalizer_residual H))
  have hPT : (P : Subgroup (residual H)).map (residual H).subtype ≤
      normalizingSylow T L₂ := by
    rw [hP, subgroupOf_map_subtype, ← d.S_intersection_residual]
    exact inf_le_left.trans (d.sourceS_le_normalizingSylow h hH)
  exact (T.isPGroup'.to_le (show normalizingSylow T L₂ ≤ (T : Subgroup G)
    from inf_le_left)).exists_sylow_sup_of_coprime_index
    (residual H) (normalizingSylow T L₂)
    (inf_le_left.trans (hH.1.1.2.trans (le_normalizer_residual H)))
    (P : Subgroup (residual H)) P.not_dvd_index hPT

/-- Source 3.1.1 gives a genuine member of H(H) over N_G(T₀). -/
theorem LocalData.common_normal_overgroup
    {T : Sylow 2 G} {L W H A B D L₂ : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D L₂) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D L₂).pCoreIn 2 ≠ ⊥) :
    normalizer (normalizingSylow T L₂ : Set G) ⊔ H ∈ Chapter1.HOver G (H : Set G) := by
  let T₀ := normalizingSylow T L₂
  let N := normalizer (T₀ : Set G)
  have hST := d.sourceS_le_normalizingSylow h hH
  have hc : H.pCoreIn 2 ≤ Global.sourceS L H :=
    Chapter3.twoCore_le_of_sylow_le T (le_inf h.sylow_normalizes hH.1.1.2)
      (show Global.intersection L H ≤ H from inf_le_right)
  have hTne : T₀ ≠ ⊥ := fun he => hH.1.1.1 (bot_unique (he ▸ hc.trans hST))
  have hTnorm : (T : Subgroup G) ≤ N :=
    (normal_subgroupOf_iff_le_normalizer (show T₀ ≤ (T : Subgroup G) from inf_le_left)).mp
      (normal_of_index_eq_two (d.normalizingSylow_index hH.1.1.2 c hd hz))
  have hTcore : T₀ ≤ N.pCoreIn 2 := le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le (show T₀ ≤ (T : Subgroup G) from inf_le_left)) T₀.le_normalizer le_rfl
  have hN : N ∈ Chapter1.HOver G (T : Set G) :=
    ⟨fun he => hTne (bot_unique (he ▸ hTcore)), hTnorm⟩
  obtain ⟨R,hRT,hR,hn⟩ := Chapter3.source_common_normal_knownSimple h.qtke T N H T₀
    hN hH.1.1 (Chapter3.HStar.hasUniqueMaximalOver T h.sylow_normalizes hH)
    hTne inf_le_left (d.normalizingSylow_sylow_in_residual_join h hH) le_rfl
  have hn' : N ⊔ H ≤ normalizer (R : Set G) := by
    simpa only [Chapter3.generated_eq_sup] using (Chapter3.normalIn_iff_le_normalizer.mp hn).2
  have hRc : R ≤ (N ⊔ H).pCoreIn 2 := le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le (hRT.trans inf_le_left))
    (hRT.trans (inf_le_left.trans
      ((show (T : Subgroup G) ≤ H from hH.1.1.2).trans le_sup_right))) hn'
  exact ⟨fun he => hR (bot_unique (he ▸ hRc)), fun _ hx => mem_sup_right hx⟩

/-- Every two-subgroup containing T₀ normalizes T₀. -/
theorem LocalData.overgroup_two_subgroup_normalizes
    {T : Sylow 2 G} {L H A B D L₂ P : Subgroup G} {p : ℕ}
    (d : LocalData T L H B D L₂) (hTH : (T : Subgroup G) ≤ H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D L₂).pCoreIn 2 ≠ ⊥)
    (hP : IsPGroup 2 P) (hTP : normalizingSylow T L₂ ≤ P) :
    P ≤ normalizer (normalizingSylow T L₂ : Set G) := by
  have hi := (two_group_over_index_two_sylow T (normalizingSylow T L₂) P inf_le_left
    (d.normalizingSylow_index hTH c hd hz) hP hTP).1
  by_cases h1 : (normalizingSylow T L₂).relIndex P = 1
  · exact (relIndex_eq_one.mp h1).trans (normalizingSylow T L₂).le_normalizer
  · have hp : (normalizingSylow T L₂).relIndex P ≠ 0 :=
      ((normalizingSylow T L₂).subgroupOf P).index_ne_zero_of_finite
    have h2 : (normalizingSylow T L₂).relIndex P = 2 := by omega
    exact (normal_subgroupOf_iff_le_normalizer hTP).mp (normal_of_index_eq_two h2)

/-- Either element of the nontrivial T/T₀ coset supplies the second
literal conjugate generating O²(H), with the explicit left-conjugation convention. -/
theorem LocalData.residual_eq_two_conjugates
    {T : Sylow 2 G} {L H A B D L₂ : Subgroup G} {p : ℕ}
    (d : LocalData T L H B D L₂) (hTH : (T : Subgroup G) ≤ H)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D L₂).pCoreIn 2 ≠ ⊥)
    {t : G} (ht : t ∈ (T : Subgroup G)) (ht0 : t ∉ normalizingSylow T L₂) :
    residual H = L₂ ⊔ L₂.map (MulAut.conj t).toMonoidHom := by
  rw [d.residual_eq_conjugateSpan, conjugateSpanBy_eq_iSup_conj]
  exact componentOrbit_eq_sup_of_index_two L₂ (T : Subgroup G) (normalizingSylow T L₂)
    (d.normalizingSylow_index hTH c hd hz) (inf_le_right.trans inf_le_right) ht ht0

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
