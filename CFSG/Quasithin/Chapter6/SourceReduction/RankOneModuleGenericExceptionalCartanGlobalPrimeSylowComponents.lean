module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeChangedSylowAction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwoSource

/-!
# Proper containing components in the prime-actor branch

The selected right factor lies in the original local component family at
T₀=N_T(L₂): its Sylow condition comes from the residual intersection,
and the original two-core of H survives in L₂T₀. A Sylow subgroup over
T₀ has index at most two, so the proved source containment theorem gives
its unique containing C-component in every intermediate subgroup between
G₀T₀ and G₀T₀B. The odd actors normalize that component. Since D moves
L₂, containment is strict. At both endpoints every defining generator
normalizes the component, giving relative normality.

No identification of T₀ with an ambient Sylow is assumed. The remaining
component-model sieve and final normalization stay with the consolidated
owner qt-d-1222-rankone-cartan-local-to-global.
Source: Aschbacher--Smith 1.2.4--5, pp.505--506, and 5.2.2, p.648.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The literal L₂T₀ has nontrivial two-core and T₀ is its Sylow subgroup. -/
theorem LocalData.right_mem_local_family
    {T : Sylow 2 G} {L W H B D L₂ : Subgroup G} {n : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D L₂) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    L₂ ∈ Chapter1.L G (normalizingSylow T L₂) := by
  let T₀ := normalizingSylow T L₂
  have hJH : L₂ ⊔ T₀ ≤ H := sup_le
    (d.right_le_residual.trans (map_subtype_le _)) (inf_le_left.trans hH.1.1.2)
  have hcore : H.pCoreIn 2 ≤ L₂ ⊔ T₀ :=
    (Chapter3.twoCore_le_of_sylow_le T (le_inf h.sylow_normalizes hH.1.1.2)
      (show Global.intersection L H ≤ H from inf_le_right)).trans
        ((d.sourceS_le_normalizingSylow h hH).trans le_sup_right)
  refine ⟨d.right_component,
    (d.normalizingSylow_sylow_in_residual_join h hH).restrict le_sup_right
      (sup_le_sup_right d.right_le_residual T₀), ?_⟩
  intro hz
  exact hH.1.1.1 (bot_unique (((le_inf hcore le_rfl).trans
    (inf_pCoreIn_le_of_le 2 hJH)).trans hz.le))

private theorem odd_is_twoPerfect {A : Type*} [Group A] [Finite A]
    (ho : Odd (Nat.card A)) : IsPPerfect 2 A := by
  intro N hn htwo
  let := hn
  apply index_eq_one.mp
  change Nat.card (A ⧸ N) = 1
  apply htwo.card_eq_or_dvd.resolve_right
  intro hd
  exact ho.not_two_dvd_nat (hd.trans N.card_quotient_dvd_card)

/-- Source containment supplies a unique proper overcomponent; T₀ and the
actual odd actors normalize it. -/
theorem LocalData.intermediate_overcomponent
    {T : Sylow 2 G} {L W H A B D L₂ X : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D L₂) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D L₂).pCoreIn 2 ≠ ⊥)
    (hsmall : generated L H D L₂ ⊔ normalizingSylow T L₂ ≤ X)
    (hbig : X ≤ extension T L H B D L₂) :
    ∃ K : Subgroup G, L₂ < K ∧ K ≤ X ∧ (K.subgroupOf X).IsCComponent ∧
      normalizingSylow T L₂ ⊔ D ⊔ (B ⊓ X) ≤ normalizer (K : Set G) ∧
      (∀ J : Subgroup G, J ≤ X → (J.subgroupOf X).IsCComponent → L₂ ≤ J → J = K) := by
  let T₀ := normalizingSylow T L₂
  have hTX : T₀ ≤ X := le_sup_right.trans hsmall
  have hRX : L₂ ≤ X := le_sup_left.trans (le_sup_right.trans (le_sup_left.trans hsmall))
  have hDX : D ≤ X := le_sup_left.trans (le_sup_left.trans hsmall)
  have hQX := (Chapter3.sqtk_of_mem_H h.qtke (d.extension_core_ne_bot hz)).subgroup (X.subgroupOf (extension T L H B D L₂))
  have hQ : IsSQTK KnownSimple.IsKnownSimple X :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hbig)).mp hQX
  have hQbar : IsSQTK KnownSimple.IsKnownSimple (X ⧸ pCore 2 X) := by
    refine ⟨?_, hQ.isKGroup.quotient _⟩
    intro q hq ho
    let : Fact q.Prime := ⟨hq⟩
    exact (primeRank_quotient_le_of_isTwoGroup q ho (pCore 2 X) pCore_isPGroup).trans
      (hQ.stronglyQuasithin q hq ho)
  have hp : IsPGroup 2 (T₀.subgroupOf X) :=
    (T.isPGroup'.to_le (show T₀ ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  have hTP : T₀ ≤ (P : Subgroup X).map X.subtype := by
    simpa only [map_subgroupOf_eq_of_le hTX] using map_mono (f := X.subtype) hP
  have hi : (T₀.subgroupOf X).relIndex (P : Subgroup X) ≤ 2 := by
    rw [show T₀.subgroupOf X = T₀.comap X.subtype from rfl, relIndex_comap]
    exact (two_group_over_index_two_sylow T T₀ _ inf_le_left
      (d.normalizingSylow_index hH.1.1.2 c hd hz) (P.isPGroup'.map X.subtype) hTP).1
  have hlocal : L₂.subgroupOf X ∈ Chapter1.L X (T₀.subgroupOf X) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTX hRX).mp ⟨hRX,d.right_mem_local_family h hH⟩
  obtain ⟨K,hK,hu⟩ := Chapter1.Section02.index_le_two_local_component_source hQbar P hP hi hlocal
  let K' := K.map X.subtype
  have hKX : K' ≤ X := map_subtype_le _
  have hKK : K'.subgroupOf X = K := comap_map_eq_self_of_injective X.subtype_injective K
  have hRK : L₂ ≤ K' := by
    simpa only [map_subgroupOf_eq_of_le hRX] using map_mono (f := X.subtype) hK.2
  have hunique : ∀ J : Subgroup G, J ≤ X →
      (J.subgroupOf X).IsCComponent → L₂ ≤ J → J = K' := by
    intro J hJX hJ hRJ
    have he := hu (J.subgroupOf X) ⟨hJ,subgroupOf_mono X hRJ⟩
    simpa only [map_subgroupOf_eq_of_le hJX] using congrArg (map X.subtype) he
  have hnorm : ∀ Y : Subgroup G, Y ≤ X →
      Y.subgroupOf X ≤ normalizer (K : Set X) → Y ≤ normalizer (K' : Set G) := by
    intro Y hYX hy
    rw [← hKK, ← subgroupOf_normalizer_eq hKX] at hy
    intro y hyY
    exact hy (show (⟨y,hYX hyY⟩ : X) ∈ Y.subgroupOf X from hyY)
  have hTnorm : T₀ ≤ normalizer (K' : Set G) := by
    apply hnorm T₀ hTX
    apply cComponent_le_normalizer_of_unique hK.1 hK.2 (fun J hJ hRJ => hu J ⟨hJ,hRJ⟩)
    rw [← subgroupOf_normalizer_eq hRX]
    exact subgroupOf_mono X inf_le_right
  have hoddnorm : ∀ Y : Subgroup G, Y ≤ X → Odd (Nat.card Y) →
      Y ≤ normalizer (K' : Set G) := by
    intro Y hYX hYo
    apply hnorm Y hYX
    apply Chapter1.Section02.twoPerfect_normalizes_cComponent_source hQbar hK.1
    apply odd_is_twoPerfect
    simpa only [Nat.card_congr (subgroupOfEquivOfLe hYX).toEquiv] using hYo
  have hDodd : Odd (Nat.card D) := by
    rw [hd.card]
    rcases hd.prime with rfl | rfl <;> decide
  have hDnorm := hoddnorm D hDX hDodd
  have hBodd : Odd (Nat.card B) := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe c.right_le).toEquiv]
    exact OddHall.odd_hall_odd c.right_hall
  have hBnorm := hoddnorm (B ⊓ X) inf_le_right
    (hBodd.of_dvd_nat (card_dvd_of_le (show B ⊓ X ≤ B from inf_le_left)))
  refine ⟨K',lt_of_le_of_ne hRK ?_,hKX,hKK.symm ▸ hK.1,
    sup_le (sup_le hTnorm hDnorm) hBnorm,hunique⟩
  · intro he
    exact d.prime_actor_not_normalizes_right h hH c hd hz (he ▸ hDnorm)

/-- The containing component is normal in the literal source group G₀T₀. -/
theorem LocalData.source_overcomponent
    {T : Sylow 2 G} {L W H A B D L₂ : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D L₂) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D L₂).pCoreIn 2 ≠ ⊥) :
    ∃ K : Subgroup G, L₂ < K ∧ K ≤ generated L H D L₂ ⊔ normalizingSylow T L₂ ∧
      (K.subgroupOf (generated L H D L₂ ⊔ normalizingSylow T L₂)).IsCComponent ∧
      (K.subgroupOf (generated L H D L₂ ⊔ normalizingSylow T L₂)).Normal ∧
      (∀ J : Subgroup G, J ≤ generated L H D L₂ ⊔ normalizingSylow T L₂ →
        (J.subgroupOf (generated L H D L₂ ⊔ normalizingSylow T L₂)).IsCComponent →
        L₂ ≤ J → J = K) := by
  obtain ⟨K,hRK,hKX,hK,hN,hu⟩ :=
    d.intermediate_overcomponent h hH c hd hz le_rfl le_sup_left
  have hTN : normalizingSylow T L₂ ≤ normalizer (K : Set G) :=
    (le_sup_left.trans le_sup_left).trans hN
  have hDN : D ≤ normalizer (K : Set G) := (le_sup_right.trans le_sup_left).trans hN
  have hRN : L₂ ≤ normalizer (K : Set G) := hRK.le.trans K.le_normalizer
  have hSN : Global.sourceS L H ≤ normalizer (K : Set G) :=
    (d.sourceS_le_normalizingSylow h hH).trans hTN
  exact ⟨K,hRK,hKX,hK,(normal_subgroupOf_iff_le_normalizer hKX).mpr
    (sup_le (sup_le hDN (sup_le hRN hSN)) hTN),hu⟩

/-- Both odd actors normalize the unique containing component in G₀T₀B;
its defining generators therefore give relative normality without identifying T₀
with an ambient Sylow subgroup. -/
theorem LocalData.extension_overcomponent
    {T : Sylow 2 G} {L W H A B D L₂ : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D L₂) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D L₂).pCoreIn 2 ≠ ⊥) :
    ∃ K : Subgroup G, L₂ < K ∧ K ≤ extension T L H B D L₂ ∧
      (K.subgroupOf (extension T L H B D L₂)).IsCComponent ∧
      (K.subgroupOf (extension T L H B D L₂)).Normal ∧
      (∀ J : Subgroup G, J ≤ extension T L H B D L₂ →
        (J.subgroupOf (extension T L H B D L₂)).IsCComponent → L₂ ≤ J → J = K) := by
  obtain ⟨K,hRK,hKX,hK,hN,hu⟩ :=
    d.intermediate_overcomponent h hH c hd hz le_sup_left le_rfl
  have hTN : normalizingSylow T L₂ ≤ normalizer (K : Set G) :=
    (le_sup_left.trans le_sup_left).trans hN
  have hDN : D ≤ normalizer (K : Set G) := (le_sup_right.trans le_sup_left).trans hN
  have hBN : B ≤ normalizer (K : Set G) := by
    rw [inf_eq_left.mpr (show B ≤ extension T L H B D L₂ from le_sup_right)] at hN
    exact le_sup_right.trans hN
  have hRN : L₂ ≤ normalizer (K : Set G) := hRK.le.trans K.le_normalizer
  have hSN : Global.sourceS L H ≤ normalizer (K : Set G) :=
    (d.sourceS_le_normalizingSylow h hH).trans hTN
  exact ⟨K,hRK,hKX,hK,(normal_subgroupOf_iff_le_normalizer hKX).mpr
    (sup_le (sup_le (sup_le hDN (sup_le hRN hSN)) hTN) hBN),hu⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
