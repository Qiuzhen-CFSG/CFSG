module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalMovementAt
public import Theory.GroupTheory.ReducedNormal.SylowCenterClosure
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.FrattiniQuotient

/-!
# The original H-star omega module and its centralizer kernel

The orbit V_H = ⟨Ω₁(Z(T))ᴴ⟩ is reduced by characteristic two and B.2.14.
Its centralizer is normal in H. Residual escape puts that centralizer in
B.6.8's maximal-overgroup core; intersecting with T gives exactly O₂(H).
A nontrivial point of Z∩V and TI also put the centralizer in the normal
core of N_H(V). In particular O₂(H) normalizes every H-conjugate of V.

This proves the 12.2.7(1) slice used in 12.2.18–19 on the original
subgroups, without movement, solvability or a residual-model assumption.
The printed C_T(V) in 12.2.7(1) is read as C_T(V_H), as required by its
explicit use in 12.2.18. The final application identifies nontriviality
of the literal V image in H/C_H(V_H) with movement outside O₂(H).
The residual identification and module alternatives of 12.2.7(2–3)
remain separate obligations of qt-d-12213-hstar-natural.

Source: Aschbacher–Smith, 12.2.7(1), 12.2.18–19, printed pp.797,800–801;
B.2.14 and B.6.8(5–6), printed pp.78,114–115.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H : Subgroup G}

/-- The source module V_H = ⟨Ω₁(Z(T))ᴴ⟩, on its original ambient carrier. -/
def hstarOmegaModule (T : Sylow 2 G) (H : Subgroup G) : Subgroup G :=
  conjugateSpanBy (omegaCenterIn (T : Subgroup G)) H

omit [Finite G] in
private theorem omega_le_sylow : omegaCenterIn (T : Subgroup G) ≤ (T : Subgroup G) :=
  fun _ hz => ((mem_omegaCenterIn_iff _ _).mp hz).1

omit [Finite G] in
theorem hstarOmegaModule_le (hTH : (T : Subgroup G) ≤ H) : hstarOmegaModule T H ≤ H :=
  conjugateSpanBy_le_self (omega_le_sylow.trans hTH)

/-- B.2.14 on the original H-star carrier. Normality is relative to H. -/
theorem chosen_hstar_omega_reduced
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    IsPReduced 2 ((hstarOmegaModule T H).subgroupOf H) := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  let S := T.subtype hTH
  have hz : Stellmacher.omegaOneCenterAmbient (S : Subgroup H) =
      (omegaCenterIn (T : Subgroup G)).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [← Stellmacher.omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le (omega_le_sylow.trans hTH)]
    change Stellmacher.omegaOneCenterAmbient (((T : Subgroup G).subgroupOf H).map H.subtype) = _
    rw [map_subgroupOf_eq_of_le hTH]
    rfl
  have hc := Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T) hH.1.1)
  have hr := omegaCenter_normalClosure_reduced S hc
  rw [hz, normalClosure_subgroupOf_eq_conjugateSpanBy _ H (omega_le_sylow.trans hTH)] at hr
  exact hr

theorem chosen_hstar_omega_elementary
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    IsElementaryAbelian 2 (hstarOmegaModule T H) := by
  let := (chosen_hstar_omega_reduced h hH).elementary
  have he : IsElementaryAbelian 2 (((hstarOmegaModule T H).subgroupOf H).map H.subtype) :=
    IsElementaryAbelian.map H.subtype
  rwa [map_subgroupOf_eq_of_le (hstarOmegaModule_le hH.1.1.2)] at he

theorem chosen_hstar_omega_le_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    hstarOmegaModule T H ≤ H.pCoreIn 2 := by
  have he := map_mono (f := H.subtype) (chosen_hstar_omega_reduced h hH).le_pCore
  rwa [map_subgroupOf_eq_of_le (hstarOmegaModule_le hH.1.1.2)] at he

theorem chosen_hstar_core_centralizes_omega
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    H.pCoreIn 2 ≤ centralizer (hstarOmegaModule T H : Set G) := by
  apply le_centralizer_iff.mp
  have he := (map_mono (f := H.subtype)
    (chosen_hstar_omega_reduced h hH).le_centralizer_pCore).trans
      (map_centralizer_le_centralizer_image _ _)
  rwa [map_subgroupOf_eq_of_le (hstarOmegaModule_le hH.1.1.2)] at he

/-- C_H(V_H) lies in the actual normal core of N_H(V). -/
theorem chosen_hstar_omega_centralizer_le_normalCore_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    centralizer ((hstarOmegaModule T H).subgroupOf H : Set H) ≤
      ((normalizer (V : Set G)).subgroupOf H).normalCore := by
  let := (chosen_hstar_omega_reduced h hH).normal
  apply normal_le_normalCore.mpr
  have hi := inf_omegaCenterIn_ne_bot_of_normalized_twoGroup V (T : Subgroup G)
    D.le_sylow T.isPGroup' (((structural L h).2.2 V D).1) D.ne_bot
  obtain ⟨v,hv,hv1⟩ := (V ⊓ omegaCenterIn (T : Subgroup G)).bot_or_exists_ne_one.resolve_left hi
  intro c hc
  apply hTI.centralizer_le_normalizer hv.1 hv1
  apply mem_centralizer_singleton_iff.mpr
  have hvW : v ∈ hstarOmegaModule T H := le_conjugateSpanBy _ _ hv.2
  exact (congrArg H.subtype (mem_centralizer_iff.mp hc
    ⟨v,hstarOmegaModule_le hH.1.1.2 hvW⟩ hvW)).symm

/-- The centralizer kernel lies in the unique maximal-overgroup core. -/
theorem chosen_hstar_omega_centralizer_le_parabolicCore_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    centralizer ((hstarOmegaModule T H).subgroupOf H : Set H) ≤
      ChapterB.minimalParabolicCore (T.subtype hH.1.1.2)
        (chosen_hstar_minimalParabolic_at h D structural hTI hH) := by
  let := (chosen_hstar_omega_reduced h hH).normal
  apply ChapterB.minimalParabolic_normal_le_core_of_residual_not_le
  intro hk
  apply chosen_hstar_residual_escape_at h structural hH
  apply le_trans _ (chosen_omega_centralizer_le_of_noEscape_at h D structural hnone)
  rintro _ ⟨k,hk',rfl⟩ z hz
  have hzW : z ∈ hstarOmegaModule T H := le_conjugateSpanBy _ _ hz
  exact congrArg H.subtype (mem_centralizer_iff.mp (hk hk')
    ⟨z,hstarOmegaModule_le hH.1.1.2 hzW⟩ hzW)

/-- The source-correct equality in 12.2.7(1) is C_T(V_H)=O₂(H). -/
theorem chosen_hstar_sylow_centralizer_omega_eq_core_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    (T : Subgroup G) ⊓ centralizer (hstarOmegaModule T H : Set G) = H.pCoreIn 2 := by
  apply le_antisymm
  · intro t ht
    have hc : (⟨t,hH.1.1.2 ht.1⟩ : H) ∈
        centralizer ((hstarOmegaModule T H).subgroupOf H : Set H) := by
      intro w hw
      exact Subtype.ext (ht.2 w hw)
    have hk := chosen_hstar_omega_centralizer_le_parabolicCore_at h D structural hnone hTI hH hc
    have hm : (⟨t,hH.1.1.2 ht.1⟩ : H) ∈
        ((T.subtype hH.1.1.2 : Sylow 2 H) : Subgroup H) ⊓
          ChapterB.minimalParabolicCore _ (chosen_hstar_minimalParabolic_at h D structural hTI hH) :=
      ⟨ht.1,hk⟩
    rw [ChapterB.minimalParabolic_sylow_inf_core] at hm
    exact mem_map_of_mem H.subtype hm
  · refine le_inf ?_ (chosen_hstar_core_centralizes_omega h hH)
    have hh := pCoreIn_le_sylow H (T.subtype hH.1.1.2)
    change H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh

/-- The two-core normalizes every original H-conjugate of the chosen module. -/
theorem chosen_hstar_core_normalizes_conjugate_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (g : H) : H.pCoreIn 2 ≤ normalizer (V.map (MulAut.conj (g : G)).toMonoidHom : Set G) := by
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow H (T.subtype hH.1.1.2)
    change H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hn : H ≤ normalizer (H.pCoreIn 2 : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have he := mem_normalizer_iff_map_conj_eq.mp (hn g.property)
  rw [← map_equiv_normalizer_eq V (MulAut.conj (g : G))]
  exact he ▸ map_mono (f := (MulAut.conj (g : G)).toMonoidHom)
    (hQT.trans (((structural L h).2.2 V D).1))

/-- The source star image is nontrivial exactly when V leaves O₂(H).
The quotient uses the literal pointwise kernel C_H(V_H). -/
theorem chosen_hstar_star_movement_iff_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    letI := (chosen_hstar_omega_reduced h hH).normal
    (V.subgroupOf H).map
      (QuotientGroup.mk' (centralizer ((hstarOmegaModule T H).subgroupOf H : Set H))) ≠ ⊥ ↔
        ¬ V ≤ H.pCoreIn 2 := by
  let := (chosen_hstar_omega_reduced h hH).normal
  rw [Ne, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  apply not_congr
  constructor
  · intro hc v hv
    rw [← chosen_hstar_sylow_centralizer_omega_eq_core_at h D structural hnone hTI hH]
    refine ⟨D.le_sylow hv, ?_⟩
    intro w hw
    exact congrArg H.subtype (hc (show (⟨v,hH.1.1.2 (D.le_sylow hv)⟩ : H) ∈
      V.subgroupOf H from hv) ⟨w,hstarOmegaModule_le hH.1.1.2 hw⟩ hw)
  · intro hv v hv' w hw
    exact Subtype.ext (chosen_hstar_core_centralizes_omega h hH (hv hv') w hw)

/-- The star kernel has precisely the original two-core as its two-core,
with normality relative to the actual H carrier. -/
theorem chosen_hstar_omega_centralizer_pCore
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    (centralizer ((hstarOmegaModule T H).subgroupOf H : Set H)).pCoreIn 2 = pCore 2 H := by
  let C := centralizer ((hstarOmegaModule T H).subgroupOf H : Set H)
  let := (chosen_hstar_omega_reduced h hH).normal
  have hQC : pCore 2 H ≤ C := by
    intro q hq w hw
    exact Subtype.ext (chosen_hstar_core_centralizes_omega h hH
      (mem_map_of_mem H.subtype hq) w hw)
  apply le_antisymm
  · change (pCore 2 C).map C.subtype ≤ pCore 2 H
    exact le_sSup ⟨ConjAct.normal_of_characteristic_of_normal, pCore_isPGroup.map C.subtype⟩
  · exact le_pCoreIn_of_normalizes pCore_isPGroup hQC
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
