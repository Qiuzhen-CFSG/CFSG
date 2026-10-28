module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.NormalityReduction
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Theory.GroupTheory.CharacteristicCentralizerSylow
public import Theory.GroupTheory.ElementaryThompsonNormalizerControl
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.ThompsonGeneration
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.CoreCentrality

/-!
# Thompson heredity and the small local branch

Thompson heredity along Q ≤ T_v ≤ T proves 12.6.7(1). If J(T_v) ≤ Q,
normalizer control forces every containing Sylow subgroup of G_v to equal
T_v, giving R=R_v and all three Thompson equalities of 12.6.8.
In the equal-residual branch the actual G_v-conjugate span of V_v lies in
the omega center of O₂(G_v). A relative Frattini argument shows exactly
which centralization conclusion would force the escaping centralizer into M.

The explicit N_G(J(Q)) ≤ M premise is discharged in ThompsonSource using
original Section12.2 normalizer control. The elementary span and all maps
remain those of the original ambient group.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
Lemmas 12.6.7--8 and the small branch of 12.6.11, printed pp.824--825.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- Source 12.6.7(1), on the original Q and T_v. -/
theorem thompson_eq_of_le_core (chosen : Section02.ChosenModule T L V) (v : V)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ Q T L) :
    elementaryAbelianMaxJ (T : Subgroup G) = elementaryAbelianMaxJ (Q T L) ∧
      elementaryAbelianMaxJ (Q T L) = elementaryAbelianMaxJ (Tv T (v : G)) := by
  have hQT : Q T L ≤ (T : Subgroup G) := (Q_le_Tv chosen v).trans inf_le_left
  have hQ := elementaryAbelianMaxJ_eq_of_intermediate (T : Subgroup G) (Q T L) hJ hQT
  have hTv := elementaryAbelianMaxJ_eq_of_intermediate (T : Subgroup G) (Tv T (v : G))
    (hJ.trans (Q_le_Tv chosen v)) inf_le_left
  exact ⟨hQ.symm,hQ.trans hTv.symm⟩

/-- Source 12.6.8 with S an actual Sylow subgroup of G_v. The source
Sylow position is the one constructed in PreferredPoint. -/
theorem SourceHypothesis.nonsingular_small_thompson_of_normalizer
    [IsElementaryAbelian 2 V]
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (hNQ : normalizer (elementaryAbelianMaxJ (Q T L) : Set G) ≤ M L)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTv : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L)
    (S : Sylow 2 (Gv (v : G)))
    (hTvS : Tv T (v : G) ≤ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) :
    let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
    S₀ = Tv T (v : G) ∧
      R L (Kv (v : G)) S₀ (v : G) = Rv T L (v : G) ∧
      elementaryAbelianMaxJ (Tv T (v : G)) = elementaryAbelianMaxJ (Rv T L (v : G)) ∧
      elementaryAbelianMaxJ (Rv T L (v : G)) = elementaryAbelianMaxJ (Q T L) ∧
      normalizer (elementaryAbelianMaxJ S₀ : Set G) ≤ M L := by
  let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  have hT := H.chosen.sylow_normalizes_component
  have hJQ : elementaryAbelianMaxJ (Tv T (v : G)) = elementaryAbelianMaxJ (Q T L) :=
    (elementaryAbelianMaxJ_eq_of_intermediate _ _ hJ (Q_le_Tv H.chosen v)).symm
  have hJN : normalizer (elementaryAbelianMaxJ (Tv T (v : G)) : Set G) ≤ M L := by
    rw [hJQ]
    exact hNQ
  have hN : normalizer (Tv T (v : G) : Set G) ≤ M L :=
    (normalizer_le_normalizer_elementaryAbelianMaxJ _).trans hJN
  have hS : S₀ = Tv T (v : G) := by
    apply prime_overgroup_eq_of_normalizer_control (Tv T (v : G)) (Gv (v : G)) (M L) hN
      ?_ S₀ (S.isPGroup'.map _) hTvS (map_subtype_le _)
    intro B hB hTB hBG hBM
    exact (Chapter1.isSylowIn_iff.mp hTv).2.2 B hB hTB (le_inf hBM hBG)
  obtain ⟨P,hP⟩ := hTv.restrict
    (show Tv T (v : G) ≤ LT T L ⊓ Gv (v : G) from inf_le_inf le_sup_right le_rfl)
    (show LT T L ⊓ Gv (v : G) ≤ Mv L (v : G) from
      inf_le_inf (sup_le L.le_normalizer hT) le_rfl)
  have hR : Rv T L (v : G) ≤ Tv T (v : G) := (pCoreIn_le_sylow _ P).trans hP.le
  have hJR : elementaryAbelianMaxJ (Rv T L (v : G)) = elementaryAbelianMaxJ (Tv T (v : G)) :=
    elementaryAbelianMaxJ_eq_of_intermediate _ _ (hJ.trans (Q_le_Rv H.chosen v)) hR
  obtain ⟨⟨e⟩,_,_,hLK⟩ := D.nonsingular_local_structure H.chosen H.source.quasisimple v hv
  have hcap := R_inf_Tv_eq_Rv T L (Kv (v : G)) S₀ (v : G) hT hLK hTvS P hP
    (Lv_coreQuotient_center_eq_bot_of_A6 L (v : G) e)
  have hRR : R L (Kv (v : G)) S₀ (v : G) = Rv T L (v : G) := by
    have hr := (R_le_S L (Kv (v : G)) S₀ (v : G)).trans hS.le
    rwa [inf_eq_left.mpr hr] at hcap
  refine ⟨hS,hRR,hJR.symm,hJR.trans hJQ,?_⟩
  change normalizer (elementaryAbelianMaxJ S₀ : Set G) ≤ M L
  rw [hS]
  exact hJN

end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- In the small Thompson case, the full G_v-conjugate span of V_v is a
normal elementary subgroup of the center of O₂(G_v). -/
theorem SourceHypothesis.small_thompson_closure_le_omega_of_normalizer
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (hNQ : normalizer (elementaryAbelianMaxJ (Q T L) : Set G) ≤ M L)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTv : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L)
    (heq : Lv L (v : G) = Kv (v : G)) :
    componentOrbit (Vv L V (v : G)) (Gv (v : G)) ≤
      omegaOneAmbient ((center ((Gv (v : G)).pCoreIn 2)).map
        ((Gv (v : G)).pCoreIn 2).subtype) := by
  let A := Gv (v : G)
  let P := A.pCoreIn 2
  let W := Vv L V (v : G)
  let ZP := (center P).map P.subtype
  have hAP : A ≤ normalizer (P : Set G) :=
    A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  obtain ⟨S,hTS,_⟩ := exists_sylow_with_Lv_normalizer T L H.chosen.sylow_normalizes_component (v : G)
  obtain ⟨_,hR,_,_,_⟩ := H.nonsingular_small_thompson_of_normalizer hNQ D v hv hTv hJ S hTS
  let S₀ := (S : Subgroup A).map A.subtype
  have hPS : P ≤ S₀ := pCoreIn_le_sylow A S
  have hPA : P ≤ (Kv (v : G) ⊔ S₀).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 A) (hPS.trans le_sup_right)
      ((sup_le (Kv_le_Gv _) (map_subtype_le _)).trans hAP)
  have hPR : P ≤ Rv T L (v : G) :=
    (hPA.trans (core_le_R_of_sylow L (Kv (v : G)) (v : G) S (Kv_le_Gv _))).trans hR.le
  have hWP : W ≤ P := by
    apply Vv_le_core_Gv_of_normalized H.chosen v
    rw [heq]
    exact (normal_subgroupOf_iff_le_normalizer (Kv_le_Gv _)).mp (Kv_normalIn_Gv _)
  have hWZ : W ≤ ZP := by
    intro w hw
    refine ⟨⟨w,hWP hw⟩,?_,rfl⟩
    change (⟨w,hWP hw⟩ : P) ∈ center P
    rw [mem_center_iff]
    intro q
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (H.Rv_centralizes_moved D v hv hTV (hPR q.property)) w hw).symm
  let := Vv_elementary H.chosen.normalizes (v : G)
  have hWO : W ≤ omegaOneAmbient ZP := by
    rw [←omegaOneAmbient_eq_self W]
    exact omegaOneAmbient_mono hWZ
  have hAZ : A ≤ normalizer (ZP : Set G) :=
    hAP.trans (normalizer_le_normalizer_characteristic_image P (center P))
  let : (omega₁ ZP (p := 2)).Characteristic := omega₁_characteristic ZP
  have hAO : A ≤ normalizer (omegaOneAmbient ZP : Set G) :=
    hAZ.trans (normalizer_le_normalizer_characteristic_image ZP (omega₁ ZP (p := 2)))
  exact iSup_conjugates_le_of_le_normalizer W A (omegaOneAmbient ZP) hWO hAO

end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The actual conjugate span is elementary; its action is still ambient conjugation. -/
theorem SourceHypothesis.small_thompson_closure_elementary_of_normalizer
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (hNQ : normalizer (elementaryAbelianMaxJ (Q T L) : Set G) ≤ M L)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTv : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L)
    (heq : Lv L (v : G) = Kv (v : G)) :
    IsElementaryAbelian 2 (componentOrbit (Vv L V (v : G)) (Gv (v : G))) := by
  let P := (Gv (v : G)).pCoreIn 2
  let ZP := (center P).map P.subtype
  let : IsMulCommutative ZP := inferInstance
  let : IsElementaryAbelian 2 (omega₁ ZP (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative ZP
  let : IsElementaryAbelian 2 (omegaOneAmbient ZP) := IsElementaryAbelian.map _
  exact IsElementaryAbelian.of_le (H.small_thompson_closure_le_omega_of_normalizer hNQ D v hv hTV hTv hJ heq)

end CFSG.Quasithin.Chapter12.Section06
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

omit [IsElementaryAbelian 2 V] in
/-- The non-small local Thompson branch already forces global Thompson
movement; only its stronger local-generation conclusion needs 12.6.6. -/
theorem SourceHypothesis.global_thompson_generation_of_local_not_le_core
    {K : GroupClass} (H : SourceHypothesis K T L V) (v : V)
    (hJ : ¬ elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L) :
    L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  apply H.eq_commutator_thompson_of_not_le_core
  intro hJT
  have he := (thompson_eq_of_le_core H.chosen v hJT).2.symm
  apply hJ
  rw [he]
  exact sSup_le fun _ hA => hA.1

/-- The small Thompson branch cannot centralize a G_v-invariant overmodule
of the literal V_v once its point centralizer is controlled. This is the
Frattini contradiction in 12.6.11, with its module-theoretic input explicit. -/
theorem SourceHypothesis.small_thompson_moves_normal_overmodule_of_normalizer
    {K : GroupClass}
    (H : SourceHypothesis K T L V)
    (hNQ : normalizer (elementaryAbelianMaxJ (Q T L) : Set G) ≤ M L)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTv : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L)
    (hescape : ¬ Gv (v : G) ≤ M L)
    (hC : Gv (v : G) ⊓ centralizer (Vv L V (v : G) : Set G) ≤ M L)
    (U : Subgroup G) (hWU : Vv L V (v : G) ≤ U)
    (hn : Gv (v : G) ≤ normalizer (U : Set G)) :
    ¬ elementaryAbelianMaxJ (Tv T (v : G)) ≤ centralizer (U : Set G) := by
  obtain ⟨S,hTS,_⟩ := exists_sylow_with_Lv_normalizer T L H.chosen.sylow_normalizes_component (v : G)
  obtain ⟨hS,_,_,_,hN⟩ := H.nonsingular_small_thompson_of_normalizer hNQ D v hv hTv hJ S hTS
  intro hcentral
  apply hescape
  apply le_of_thompson_normalizer_centralizer_control (Gv (v : G)) (M L) U S hn
    ((inf_le_inf le_rfl (Subgroup.centralizer_le hWU)).trans hC) ?_ hN
  rwa [hS]

end CFSG.Quasithin.Chapter12.Section06
