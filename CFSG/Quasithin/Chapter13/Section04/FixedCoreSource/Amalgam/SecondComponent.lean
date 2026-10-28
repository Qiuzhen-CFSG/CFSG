module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondSolvableExclusion
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.Components

/-!
# The actual component of the second join

Nonsolvability constructs a C-component in the original second join Y.
The full action kernel is O₂(Y), so the component moves the same reduced
omega span. The source omega-module criterion puts it in the faithful
local family. Earlier 13.3.2 then gives T-normalization, the actual mid-size
quotient catalogue, and starred maximality. The local SQTK orbit bound
and the original Sylow subgroup promote relative subnormality to normality.

The exact component action kernel is its intrinsic two-core. No component,
normality, movement, or model marking is supplied by the caller. The earlier
Source1332OneTwo and N_G(L)=LT premises remain explicit for final assembly.
Source: Aschbacher--Smith 13.4.5 and 13.4.7(3), printed pp.898 and903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

open Section03.Noncentrality.SupercriticalSource

theorem exists_original_plane_second_component
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcentral : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂))
    (hs : Group.IsSolvable (A ⊔ B : Subgroup G))
    (hcomm : ¬ ⁅(pResidual 2 A).map A.subtype,(pResidual 2 B).map B.subtype⁆ ≤
      centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) : Set G))
    (Wplane : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hWplane : Module.finrank (ZMod 2) Wplane = 2)
    (hTplane : (T : Subgroup G) ≤ normalizer (m.naturalPreimage Wplane : Set G))
    (hBplane : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage Wplane : Set G))
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (h1332 : Source1332OneTwo T) :
    let X := A ⊔ B
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let Y₂ := (MarkedCubicRecognition.centralThreeResidual X).map X.subtype
    let Y := firstFlagNormalizer T L V ⊔ (Y₂ ⊔ (T : Subgroup G))
    let U := conjugateSpanBy Z Y
    ∃ K : Subgroup Y, K.IsCComponent ∧ K.Normal ∧
      K.map Y.subtype ∈ MainForward.faithfulLocalComponents T ∧
      K.map Y.subtype ∈ Chapter1.LStar G T ∧
      (T : Subgroup G) ≤ normalizer (K.map Y.subtype : Set G) ∧
      ⁅U,K.map Y.subtype⁆ ≠ ⊥ ∧
      MidSizeModel ((K.map Y.subtype) ⧸ pCore 2 (K.map Y.subtype)) ∧
      K ⊓ centralizer (U.subgroupOf Y : Set Y) = K.pCoreIn 2 := by
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let Y₂ := (MarkedCubicRecognition.centralThreeResidual X).map X.subtype
  let Y := firstFlagNormalizer T L V ⊔ (Y₂ ⊔ (T : Subgroup G))
  let U := conjugateSpanBy Z Y
  let Ui := U.subgroupOf Y
  have hTY : (T : Subgroup G) ≤ Y := le_sup_right.trans le_sup_right
  have hUY : U ≤ Y := conjugateSpanBy_le
    (fun z hz => hTY ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) Y.le_normalizer
  have hns := original_plane_second_nonsolvable h₀ h structural D m
    hTA hTB eA eB hne hindexL hindexA hindexB hcentral hs hcomm
    Wplane hWplane hTplane hBplane hM
  obtain ⟨_,_,_,_,_,_,_,hlocal,hred,_,_,_⟩ := original_plane_second_amalgam
    h₀ h structural D m hTA hTB eA eB hne hindexL hindexA hindexB hcentral
    hs hcomm Wplane hWplane hTplane hBplane
  have hk := (original_plane_second_action_kernel h₀ h structural D m
    hTA hTB eA eB hne hindexL hindexA hindexB hcentral hs hcomm
    Wplane hWplane hTplane hBplane hM).2
  obtain ⟨K,hK⟩ := exists_isCComponent_of_not_isSolvable hns
  let : Ui.Normal := hred.normal
  let : IsElementaryAbelian 2 Ui := hred.elementary
  have hm : ⁅Ui,K⁆ ≠ ⊥ := by
    intro hh
    have hc : K ≤ centralizer (Ui : Set Y) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh)
    rw [hk] at hc
    have hp : IsPGroup 2 K := pCore_isPGroup.to_le hc
    let : Group.IsNilpotent K := hp.isNilpotent
    exact hK.not_isSolvable inferInstance
  have hU : Ui ≤ omegaOneCenterAmbient (pCore 2 Y) := by
    intro u hu
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hred.le_pCore hu,elemPow_eq_one_of_isElementaryAbelian u hu,
        hred.le_centralizer_pCore hu⟩
  have hf : K.map Y.subtype ∈ MainForward.faithfulLocalComponents T :=
    (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T _).mpr
      (Section03.Noncentrality.source_component_faithful_local T Y hTY hlocal.1.1
        (Chapter1.lemma_1_1_4_6 T (h₀.qtke.evenCharacteristic T) hlocal.1) K Ui hK hU hm)
  have hTK := (h1332 _ hf).1
  have hn : K.Normal := by
    rcases Chapter1.Section02.component_normal_or_index_two_source
      (Chapter3.sqtk_of_mem_H h₀.qtke hlocal.1.1) hK with hn | hi
    · exact hn
    have hTN : (T : Subgroup G).subgroupOf Y ≤ normalizer (K : Set Y) := by
      have he : (K.map Y.subtype).subgroupOf Y = K :=
        comap_map_eq_self_of_injective Y.subtype_injective K
      rw [←he,←subgroupOf_normalizer_eq (map_subtype_le K)]
      exact comap_mono hTK
    have hd := index_dvd_of_le hTN
    rw [hi] at hd
    exact ((T.subtype hTY).not_dvd_index hd).elim
  refine ⟨K,hK,hn,hf,Section03.Noncentrality.source1332_faithful_maximal
    h₀.qtke T h1332 hf,hTK,?_,(h1332 _ hf).2,?_⟩
  · intro hh
    apply hm
    apply (map_eq_bot_iff_of_injective _ Y.subtype_injective).mp
    rwa [map_commutator,map_subgroupOf_eq_of_le hUY]
  · rw [hk]
    have hh := congrArg (Subgroup.map K.subtype) (hK.subnormal.pCore_subgroupOf 2)
    rwa [subgroupOf_map_subtype,inf_comm] at hh


end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
