module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeHeldCubicExcluded
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CodeHeldSix

/-!
# The original M22-code orbit escapes every H-star two-core

The preceding inside-core reduction retains only a Held containing component
with the full original involution residual quotient A₆. Restrict the same
Sylow and residual to that component and apply the literal Held exclusion.
This proves the exceptional Aut(M22)-code case of 8.2.2(1), with no `hcore`
assumption in the conclusion and no change to the original orbit or cover.

The final application supplies the genuine E.2.8 input for pair selection,
including normal-core escape and characteristic two. The later M22-code
elimination through 8.2.13 and unconditional M24-cocode selection remain
separate source obligations.

Source: Aschbacher--Smith 8.2.2(1), printed pp.714--715, and E.2.8,
refs/quasithin.pdf. The two Held covering cases retain their original
residuals, ambient normalizers and quotient maps throughout.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Chapter8.Section02.Centralizer Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

theorem sourceOrbit_m22_code_not_held_simple_section
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    {K : Subgroup G} (hK : K ∈ cComponentsIn (centralizer ({(z : G)} : Set G)))
    (hRK : localResidual L z ≤ K)
    (eR : (localResidual L z ⧸ pCore 2 (localResidual L z)) ≃* alternatingGroup (Fin 6))
    (eK : (K ⧸ pCore 2 K) ≃* Held.He) : False := by
  let C := centralizer ({(z : G)} : Set G)
  let M := normalizer (L : Set G) ⊓ C
  let R := localResidual L z
  have hRC : R ≤ C := (localResidual_le L z).trans inf_le_right
  have hRM : R ≤ M := (localResidual_le L z).trans (inf_le_inf_right _ L.le_normalizer)
  have hTC : (T : Subgroup G) ≤ C := fun t ht =>
    mem_centralizer_singleton_iff.mpr (hz t ht)
  have hRTM : R ⊔ (T : Subgroup G) ≤ M := sup_le hRM
    (le_inf D.sylow_normalizes_component hTC)
  obtain ⟨hR,_⟩ := D.sourceOrbit_m22_code_centralizer_component h d z hz hne
  have hl : R ∈ ChapterA.Section03.localCComponents (T : Subgroup G) :=
    hR.subgroupOf_of_le le_sup_left hRTM
  let S := T.subtype hTC
  have hlC : R.subgroupOf C ∈ ChapterA.Section03.localCComponents (S : Subgroup C) :=
    ChapterA.Section03.SourceEmbeddings.local_restrict hl hRC
  have hTN : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (le_inf D.sylow_normalizes_component hTC).trans (MathieuSextet.residual_normalized L z)
  have hnC : (S : Subgroup C) ≤ normalizer (R.subgroupOf C : Set C) := by
    rw [Sylow.coe_subtype,←subgroupOf_normalizer_eq hRC]
    exact comap_mono hTN
  let a : R.subgroupOf C ≃* R := subgroupOfEquivOfLe hRC
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let b : K.subgroupOf C ≃* K := subgroupOfEquivOfLe hK.1
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  exact Chapter8.MathieuShadowRows.not_held_containing_six S hlC hnC hK.2
    (comap_mono hRK) (aq.trans eR) (bq.trans eK)

/-- The exceptional original Aut(M22)-code orbit escapes the actual H-star
two-core. This is source 8.2.2(1), with no containment premise. -/
theorem sourceOrbit_m22_code_not_le_parabolic_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ¬ D.sourceOrbit ≤ H.pCoreIn 2 := by
  intro hcore
  obtain ⟨z,hne,_,hHC,_,K,_,hK,hRK,_,_,_,_,_,⟨eK⟩,_,⟨eR⟩⟩ :=
    D.sourceOrbit_m22_code_inside_core_held_simple_section h hmany hV hnon d hH hcore
  have hz : (z : G) ∈ centralizer (T : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mp (hHC (hH.1.1.2 ht))
  exact D.sourceOrbit_m22_code_not_held_simple_section h.toHypothesis1221 d z hz hne hK hRK eR eK

/-- The proved escape supplies the original E.2.8 pair-construction input,
including escape from the actual normal core and characteristic two. -/
theorem sourceOrbit_m22_code_hstar_setup
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    Chapter8.Section02.Offenders.Parabolic.Construction.HypothesisE28
      KnownSimple.IsKnownSimple H T (normalizer (L : Set G)) D.sourceOrbit ∧
        HasCharacteristicTwo H := by
  let Z := D.sourceOrbit ⊓ centralizer (T : Set G)
  have hZ : Z ≠ ⊥ := inf_centralizer_ne_bot_of_pGroups (T : Subgroup G)
    D.sourceOrbit T.isPGroup' (IsElementaryAbelian.isPGroup 2 D.sourceOrbit)
    D.sourceOrbit_weakClosure_setup.normalizes D.sourceOrbit_weakClosure_setup.nontrivial
  have hzOmega : Z ≤ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) := by
    intro z hz
    exact (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨D.sourceOrbit_weakClosure_setup.le_sylow hz.1,
        elemPow_eq_one_of_isElementaryAbelian (p := 2) z hz.1,hz.2⟩
  have hHZ : H ≤ centralizer (Z : Set G) :=
    (D.sourceOrbit_hstar_centralizes_omega h.toHypothesis1221 hnon hH).trans
      (centralizer_le hzOmega)
  have hMV : H ⊓ normalizer (L : Set G) ≤ normalizer (D.sourceOrbit : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans hHZ)).trans
      ((D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).localCentralizer_le_normalizer
        hZ (show Z ≤ D.sourceOrbit from inf_le_left))
  refine ⟨Chapter8.Section02.HermitianSource.hypothesisE28_of_HStar_outside_twoCore
    h.simpleQTKE T D.sylow_normalizes_component hH D.sourceOrbit_weakClosure_setup.le_sylow
    (normal_subgroupOf_of_le_normalizer D.sourceOrbit_weakClosure_setup.normalizes) hMV
    (D.sourceOrbit_m22_code_not_le_parabolic_core h hmany hV hnon d hH), ?_⟩
  exact Chapter1.mem_He_iff.mp
    (Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T) hH.1.1)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
