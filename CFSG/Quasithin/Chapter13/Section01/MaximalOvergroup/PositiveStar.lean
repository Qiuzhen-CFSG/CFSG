module
public import CFSG.Quasithin.Chapter3.Section02.SourceXiMinus
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness.Centralizing
public import Theory.GroupTheory.ReducedNormal.SylowCenter
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Theory.GroupTheory.PGroup.CharacteristicPairReduction
/-!
# The positive starred family has a common maximal overgroup

The genuine3.2.13 consequence of the canonical3.1.8 input makes a positive
starred Xi member nonfaithful. Its intrinsic module vanishes, so the actual
commutator bound makes it centralize R₂(XT). B.2.14 puts the original Sylow
omega-center in that reduced subgroup. Thus XT centralizes the same Z for
every member. The proved starred normalizer theorem1.3.7 and normalizer
control of this nontrivial two-subgroup give N_G(X)=!M(C_G(Z)), and hence
all positive starred members lie in one common maximal two-local subgroup.

Only the genuine earlier SourceTheorem318One remains explicit. No starred
membership is inferred from radical membership, and no3.2.14 centralization
or seven-model classification is asserted.
Source: Aschbacher--Smith, Lemma13.1.5, printed p.868, using3.2.13, A.4.11,
B.2.14 and1.3.7.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01
open Chapter1 ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G]

theorem positive_star_intrinsicModule_eq_bot
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h318 : Chapter3.SourceTheorem318One G) (T : Sylow 2 G)
    {X : Subgroup G} (hX : X ∈ Chapter3.XiPlus G (T : Subgroup G) ∩ XiStar G T) :
    intrinsicSignalizerModule X = ⊥ := by
  by_contra hn
  have hHe : X ∈ He G := hX.1.1.mem_He
    (fun _ hM _ hN hNM hnorm => lemma_1_1_3_1 hM hN hNM hnorm)
    (lemma_1_1_4_6 T (hG.evenCharacteristic T))
  have hf : X ∈ XiStarF G (T : Subgroup G) :=
    ⟨⟨hX.1.1, ⟨⟨hX.1.1.ne_bot,hX.1.1.perfect,
      generalizedFitting_eq_pCore_of_selfCentralizing 2 (mem_He_iff.mp hHe)⟩,hn⟩⟩,hX.2⟩
  exact hX.1.2 (Chapter3.SourceXiMinus.source_XiStarF_subset_XiMinus_of_318 hG h318 T hf)

theorem positive_star_centralizes_reduced
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h318 : Chapter3.SourceTheorem318One G) (T : Sylow 2 G)
    {X : Subgroup G} (hX : X ∈ Chapter3.XiPlus G (T : Subgroup G) ∩ XiStar G T) :
    X ≤ centralizer ((reducedTwoSubgroup (X ⊔ (T : Subgroup G) : Subgroup G)).map
      (X ⊔ (T : Subgroup G)).subtype : Set G) := by
  let J := X ⊔ (T : Subgroup G)
  let Y := X.subgroupOf J
  let := hX.1.1.normal_in_join
  let e : Y ≃* X := subgroupOfEquivOfLe (show X ≤ J from le_sup_left)
  have he : Y.map J.subtype = X := map_subgroupOf_eq_of_le le_sup_left
  have hzero : intrinsicSignalizerModule Y = ⊥ := by
    apply map_injective (f := J.subtype) J.subtype_injective
    rw [← intrinsicSignalizerModule_map_of_injective J.subtype J.subtype_injective,
      he, positive_star_intrinsicModule_eq_bot hG h318 T hX, Subgroup.map_bot]
  have hm : ⁅reducedTwoSubgroup J,Y⁆ = ⊥ := bot_unique
    ((reduced_commutator_le_intrinsicModule Y
      (show Y.Normal from inferInstance).isSubnormal
      (hX.1.1.perfect.of_surjective e.symm.toMonoidHom e.symm.surjective)).trans_eq hzero)
  have ha := congrArg (Subgroup.map J.subtype) hm
  rw [map_commutator,he,Subgroup.map_bot,commutator_comm] at ha
  exact commutator_eq_bot_iff_le_centralizer.mp ha

theorem positive_star_centralizes_sylowOmega
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h318 : Chapter3.SourceTheorem318One G) (T : Sylow 2 G)
    {X : Subgroup G} (hX : X ∈ Chapter3.XiPlus G (T : Subgroup G) ∩ XiStar G T) :
    X ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  let J := X ⊔ (T : Subgroup G)
  have hHe : J ∈ He G := lemma_1_1_4_6 T (hG.evenCharacteristic T)
    ⟨hX.1.1.join_mem_H,fun _ hx => mem_sup_right hx⟩
  have hi := sylow_omegaCenter_le_reduced (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right))
    (mem_He_iff.mp hHe)
  change omegaOneCenterAmbient ((T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)) : Subgroup J) ≤ reducedTwoSubgroup J at hi
  have hj := map_mono (f := J.subtype) hi
  rw [← omegaOneCenterAmbient_map_injective J.subtype J.subtype_injective,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right)] at hj
  exact (positive_star_centralizes_reduced hG h318 T hX).trans (centralizer_le hj)

theorem positive_star_centralizer_unique
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h318 : Chapter3.SourceTheorem318One G) (T : Sylow 2 G)
    {X : Subgroup G} (hX : X ∈ Chapter3.XiPlus G (T : Subgroup G) ∩ XiStar G T) :
    IsMaximalTwoLocal (normalizer (X : Set G)) ∧
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ normalizer (X : Set G) ∧
      ∀ M : Subgroup G, IsMaximalTwoLocal M →
        centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ M →
        M = normalizer (X : Set G) := by
  obtain ⟨hmax,hu⟩ := XiEmbedding.normalizer_unique_of_XiStar_knownSimple hG T hX.2
  have hunique (N : Subgroup G) (hN : IsMaximalTwoLocal N)
      (hJN : X ⊔ (T : Subgroup G) ≤ N) : N = normalizer (X : Set G) := by
    have hn : N ∈ {M : Subgroup G | IsMaximalTwoLocal M ∧ X ⊔ (T : Subgroup G) ≤ M} := ⟨hN,hJN⟩
    rw [hu] at hn
    exact Set.mem_singleton_iff.mp hn
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have hXZ : X ≤ centralizer (Z : Set G) := positive_star_centralizes_sylowOmega hG h318 T hX
  have hTZ : (T : Subgroup G) ≤ centralizer (Z : Set G) := by
    intro t ht z hz
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht |>.symm
  have hJZ : X ⊔ (T : Subgroup G) ≤ centralizer (Z : Set G) := sup_le hXZ hTZ
  have hTne : (T : Subgroup G) ≠ ⊥ := by
    have hcore := hX.1.1.pCoreIn_ne_bot
      (fun _ hM _ hN hNM hnorm => lemma_1_1_3_1 hM hN hNM hnorm)
      (lemma_1_1_4_6 T (hG.evenCharacteristic T))
    have hSyl : IsSylowIn 2 (T : Subgroup G) (X ⊔ (T : Subgroup G)) := by
      refine ⟨T.subtype le_sup_right, ?_⟩
      simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right]
    exact fun he => hcore (bot_unique ((hX.1.1.pCoreIn_le_of_isSylowIn hSyl).trans_eq he))
  let : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot (T : Subgroup G)).mpr hTne
  have hZne : Z ≠ ⊥ := by
    exact fun he => omega_center_ne_bot (G := T) T.isPGroup'
      ((((omega₁ (center T) (p := 2)).map (center T).subtype).map_eq_bot_iff_of_injective (T : Subgroup G).subtype_injective).mp he)
  let : IsElementaryAbelian 2 Z := omegaOneCenterAmbient_elementaryAbelian _
  have hNZ : normalizer (Z : Set G) ≤ normalizer (X : Set G) :=
    normalizer_le_of_unique_maximalTwoLocal hunique (IsElementaryAbelian.isPGroup 2 Z)
      hZne (hJZ.trans (Subgroup.centralizer_le_normalizer _))
  exact ⟨hmax,(Subgroup.centralizer_le_normalizer _).trans hNZ,
    fun M hM hCM => hunique M hM (hJZ.trans hCM)⟩

theorem positive_star_common_normalizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h318 : Chapter3.SourceTheorem318One G) (T : Sylow 2 G)
    (hne : (Chapter3.XiPlus G (T : Subgroup G) ∩ XiStar G T).Nonempty) :
    ∃ M : Subgroup G, IsMaximalTwoLocal M ∧
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ M ∧
      (∀ N : Subgroup G, IsMaximalTwoLocal N →
        centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ N → N = M) ∧
      ∀ X ∈ Chapter3.XiPlus G (T : Subgroup G) ∩ XiStar G T,
        X ≤ M ∧ normalizer (X : Set G) = M := by
  obtain ⟨X,hX⟩ := hne
  obtain ⟨hm,hc,hu⟩ := positive_star_centralizer_unique hG h318 T hX
  refine ⟨normalizer (X : Set G),hm,hc,hu,?_⟩
  intro Y hY
  obtain ⟨hym,hyc,_⟩ := positive_star_centralizer_unique hG h318 T hY
  have he := hu _ hym hyc
  exact ⟨Y.le_normalizer.trans_eq he,he⟩
end CFSG.Quasithin.Chapter13.Section01
