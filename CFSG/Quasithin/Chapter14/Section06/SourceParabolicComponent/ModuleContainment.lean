module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.ResidualGeneration
public import Theory.GroupTheory.PCoreOmegaMovement
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.PlaneMovement
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleResidual
public import Theory.GroupTheory.PResidual.PrimeToQuotientLift
/-!
# The original plane in the selected component module

The original first residual moves the central line, so its orbit spans the
source four-group. Characteristic two puts the line in Ω₁Z(O₂(I)), hence
puts the entire I-span there. The proved identity U=[U,O²(I)] then puts U
in [Ω₁Z(O₂(K)),K] for the same selected residual K, and consequently in
its full block module. No representation or dimension is assumed.

Source: Aschbacher--Smith 14.6.10(5), printed p.1029, the containment V≤W
before the module-geometry case analysis.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06
universe u
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open ChapterF SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type u} [Group G] [Finite G]

private theorem plane_eq_span_of_line (V Z A : Subgroup G)
    (hV : Nat.card V = 4) (hZ : Nat.card Z = 2) (hZV : Z ≤ V)
    (hn : A ≤ normalizer (V : Set G)) (hnc : ¬ A ≤ centralizer (Z : Set G)) :
    V = conjugateSpanBy Z A := by
  let D := conjugateSpanBy Z A
  have hDV : D ≤ V := conjugateSpanBy_le hZV hn
  have hZD : Z ≤ D := le_conjugateSpanBy _ _
  have hne : Z ≠ D := by
    intro he
    have hAD : A ≤ normalizer (D : Set G) := le_normalizer_conjugateSpanBy Z A
    rw [←he] at hAD
    exact hnc (hAD.trans (normalizer_le_centralizer_of_card_two Z hZ))
  have hd : Nat.card D ∣ 2 ^ 2 := by
    simpa only [hV,show 2 ^ 2 = (4 : ℕ) from rfl] using card_dvd_of_le hDV
  have hlo : 2 ≤ Nat.card D := by
    simpa only [hZ] using Nat.card_le_card_of_injective _ (inclusion_injective hZD)
  obtain ⟨k,hk,hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  interval_cases k
  · have hc1 : Nat.card D = 1 := by simpa using hc
    omega
  · exact (hne (eq_of_le_of_card_ge hZD (by rw [hZ,hc]; decide))).elim
  · exact (eq_of_le_of_card_ge hDV (by rw [hc,hV]; decide)).symm

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (hlocal : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (H ⊓ centralizer ({u} : Set G)))
include hG hempty hM hunique hmany hcard e hab H hH hu hindex hmove hproduct hU3 hlocal

/-- The actual generated module lies in the omega-center of the original two-core. -/
theorem source_parabolic_span_le_omegaCore
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (I I2 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hSI2 : (T : Subgroup G) ⊓ I ≤ I2) (hI2H : I2 ≤ H)
    (hquot2 : Nonempty ((I2 ⧸ pCore 2 I2) ≃* Equiv.Perm (Fin 3)))
    (hout : ¬ I ⊓ M ≤ Mc)
    (hgen : ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2 = I) :
    conjugateSpanBy (localModule T M) I ≤ omegaOneCenterAmbient (I.pCoreIn 2) := by
  let V := localModule T M
  let Z := centralInvolutions T
  let A := (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
    (sourceResidual M Mc ⊓ I).subtype
  have hAI : A ≤ I := (map_subtype_le _).trans inf_le_right
  have hAN : A ≤ normalizer (V : Set G) := ((map_subtype_le _).trans inf_le_left).trans
    ((sourceResidual_le M Mc).trans (le_normalizer_conjugateSpanBy _ M))
  have hcover := (source_lemma_14_6_6_3 hG T hempty hM hunique hmany hcard e hab H hH
    u hu hindex hmove hproduct I hI.1.2.1 hout).1
  have hSyl := (source_suitable_intersection_sylow hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1).1
  have hAout := (source_intersection_parabolic_data hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct I hI.1.2.1 hSyl hcover).2.2.2
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hMc,_⟩ :=
    source_lemma_14_1_18 hG T hempty hM hunique hmany hcard e
  have hspan : V = conjugateSpanBy Z A := plane_eq_span_of_line V Z A hcard
    (plane_centralInvolutions_card T M hM.1.2 hcard e) (le_conjugateSpanBy _ _) hAN
    (fun hh => hAout (hh.trans_eq hMc.symm))
  have hHMc : H ≤ Mc := by
    have he := (Section02.source_lemma_14_2_3 hG T hempty hM hunique hmany hcard e
      H hH.1 hH.2).1
    exact (show Mc ∈ maximalTwoLocalOvergroups H from he ▸ Set.mem_singleton Mc).2
  have hVU : V ≤ conjugateSpanBy V Mc := le_conjugateSpanBy _ _
  have huU : u ∈ conjugateSpanBy V Mc := (conjugateSpanBy_mono le_rfl hHMc) hu
  have hrankTwo := Section02.source_lemma_14_2_4 hG T hempty hM hunique hmany hcard e
  have hVT : V ≤ (T : Subgroup G) := by
    simpa only [Section02.rankTwoSeed_eq_localModule] using hrankTwo.seed_le_sylow
  have hVI : V ≤ I := by
    let := hab
    intro v hv
    apply hI.1.2.1
    refine ⟨hVT hv,mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg (conjugateSpanBy V Mc).subtype
      (mul_comm (⟨v,hVU hv⟩ : conjugateSpanBy V Mc) ⟨u,huU⟩)
  have hZI : Z ≤ I := (le_conjugateSpanBy _ _).trans hVI
  have hF1 := ChapterF.SourceAssembly.characteristicTwoMarked_of_large_nonabelian
    (ChapterF.SourceAssembly.Goldschmidt.largeNonabelian_of_marked_recognition
      ChapterF.SourceAssembly.Goldschmidt.radiusTwoMarkedInput
      ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree.radiusThreeMarkedInput)
  have hfit := source_lemma_14_6_10_4_of_escape hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct hU3 hlocal hF1 I I2 hI hSI2 hI2H
    hquot2 hout hgen hrank
  have hself : centralizer (pCore 2 I : Set I) ≤ pCore 2 I := by
    simpa only [hfit] using centralizer_generalizedFitting_le I
  obtain ⟨P,hP⟩ := hSyl
  have hQT : I.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow I P).trans (hP.le.trans inf_le_left)
  have hZΩ : Z ≤ omegaOneCenterAmbient (I.pCoreIn 2) := by
    intro z hz
    obtain ⟨_,hz2,hzc⟩ := (mem_omegaOneCenterAmbient_iff _ z).mp hz
    let zi : I := ⟨z,hZI hz⟩
    have hzQ : zi ∈ pCore 2 I := hself (fun a ha =>
      Subtype.ext (hzc a (hQT (mem_map_of_mem I.subtype ha))))
    exact (mem_omegaOneCenterAmbient_iff _ z).mpr
      ⟨mem_map_of_mem I.subtype hzQ,hz2,fun a ha => hzc a (hQT ha)⟩
  have hIQ : I ≤ normalizer (I.pCoreIn 2 : Set G) := I.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hIΩ : I ≤ normalizer (omegaOneCenterAmbient (I.pCoreIn 2) : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,←omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective,
      mem_normalizer_iff_map_conj_eq.mp (hIQ hg)]
  apply conjugateSpanBy_le _ hIΩ
  change V ≤ omegaOneCenterAmbient (I.pCoreIn 2)
  rw [hspan]
  exact conjugateSpanBy_le hZΩ (hAI.trans hIΩ)

/-- The actual moved module lies in the same selected component's omega-center commutator. -/
theorem source_parabolic_span_le_component_module
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (I I2 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hSI2 : (T : Subgroup G) ⊓ I ≤ I2) (hI2H : I2 ≤ H)
    (hquot2 : Nonempty ((I2 ⧸ pCore 2 I2) ≃* Equiv.Perm (Fin 3)))
    (hout : ¬ I ⊓ M ≤ Mc)
    (hgen : ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2 = I)
    (K : Subgroup I) (hKr : K = pResidual 2 I) :
    let C := K.map I.subtype
    let U := conjugateSpanBy (localModule T M) I
    U ≤ ⁅omegaOneCenterAmbient (C.pCoreIn 2),C⁆ ∧
      U ≤ (ChapterC.blockU C).map C.subtype := by
  let C := K.map I.subtype
  let U := conjugateSpanBy (localModule T M) I
  have hCI : C ≤ I := map_subtype_le _
  have hIC : I ≤ normalizer (C : Set G) := by
    change I ≤ normalizer (K.map I.subtype : Set G)
    rw [hKr]
    exact I.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image I (pResidual 2 I))
  have hm : ⁅U,C⁆ = U := by
    change ⁅conjugateSpanBy (localModule T M) I,K.map I.subtype⁆ = _
    rw [hKr]
    exact (source_parabolic_global_span_moved hG T hempty hM hunique hmany hcard e hab H hH
      u hu hindex hmove hproduct hU3 hlocal I hI.1 hout).symm
  have hΩ := source_parabolic_span_le_omegaCore hG T hempty hM hunique hmany hcard e hab H hH
    u hu hindex hmove hproduct hU3 hlocal hrank I I2 hI hSI2 hI2H hquot2 hout hgen
  have hw := moved_omegaCenter_le_core_commutator I C U hCI hIC
    (le_normalizer_conjugateSpanBy _ _) hΩ hm
  refine ⟨hw,hw.trans ?_⟩
  have hQ : omegaOneCenterAmbient (C.pCoreIn 2) ≤ C.pCoreIn 2 :=
    fun x hx => ((mem_omegaOneCenterAmbient_iff _ x).mp hx).1
  have hmod : (ChapterC.blockU C).map C.subtype = ⁅C.pCoreIn 2,C⁆ := by
    rw [ChapterC.blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype]
    rfl
  rw [hmod]
  exact commutator_mono hQ le_rfl

/-- All structural and moved-module conclusions hold for the same source component. -/
theorem source_parabolic_module_data
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (I I2 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hSI2 : (T : Subgroup G) ⊓ I ≤ I2) (hI2H : I2 ≤ H)
    (hquot2 : Nonempty ((I2 ⧸ pCore 2 I2) ≃* Equiv.Perm (Fin 3)))
    (hout : ¬ I ⊓ M ≤ Mc)
    (hgen : ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2 = I) :
    let I1 := (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)
    let q := QuotientGroup.mk' (pPrimeCore 3 I)
    let A := (I1.subgroupOf I).map q
    let B := (I2.subgroupOf I).map q
    ∃ K : Subgroup I, K.IsCComponent ∧ K.Normal ∧
      generalizedFitting K = pCore 2 K ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      K = pResidual 2 I ∧
      K.map I.subtype ⊔ ((T : Subgroup G) ⊓ I) = I ∧
      (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
        (sourceResidual M Mc ⊓ I).subtype ≤ K.map I.subtype ∧
      (let C := K.map I.subtype
       let U := conjugateSpanBy (localModule T M) I
       U ≤ ⁅omegaOneCenterAmbient (C.pCoreIn 2),C⁆ ∧
         U ≤ (ChapterC.blockU C).map C.subtype) ∧
      ¬ ChapterC.IsChiZeroBlock K ∧
      (∀ B : Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.BinaryField, ¬ Nonempty ((K ⧸ pCore 2 K) ≃* SL(2,B.Carrier))) ∧
      ¬ K.map I.subtype ≤ I ⊓ M ∧
      Input KnownSimple.IsKnownSimple I (I1.pCoreIn 2) (I ⊓ M) (K.map I.subtype) ∧
      ChapterC.C27Source.SmallModels.Model
        (starImage (K.map I.subtype) (I1.pCoreIn 2) (K.map I.subtype)) ∧
      IsComponent (I ⧸ pPrimeCore 3 I) (K.map q) ∧
      (let C := K.map I.subtype
       let a := K.equivMapOfInjective I.subtype I.subtype_injective
       ∃ e : (starImage C (I1.pCoreIn 2) C ⧸ center (starImage C (I1.pCoreIn 2) C)) ≃*
           ((K.map q) ⧸ center (K.map q)),
         ∀ k : K, e (QuotientGroup.mk' (center (starImage C (I1.pCoreIn 2) C))
             (toStarImage C (I1.pCoreIn 2) (a k))) =
           QuotientGroup.mk' (center (K.map q)) (q.subgroupMap K k)) ∧
      ∃ S : Sylow 2 (I ⧸ pPrimeCore 3 I), A ⊓ B = (S : Subgroup _) ∧
        (FSource.SourceAlternative A B S ∨ FSource.SourceAlternative B A S) ∧
        (K.map q = generalizedFitting (I ⧸ pPrimeCore 3 I) ∧
          IsQuasisimple (generalizedFitting (I ⧸ pPrimeCore 3 I))) := by
  obtain ⟨K,hK,hn,hfit,hq,hKr,hsup,hLI,hchi,hbin,ho,hi,hm,himage,hcomp,S,hS,hsource,hcase⟩ :=
    source_parabolic_residual_data hG T hempty hM hunique hmany hcard e hab H hH u hu
      hindex hmove hproduct hU3 hlocal hcoreIndex hrank I I2 hI hSI2 hI2H hquot2 hout hgen
  have hmod := source_parabolic_span_le_component_module hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal hrank I I2 hI hSI2 hI2H
    hquot2 hout hgen K hKr
  exact ⟨K,hK,hn,hfit,hq,hKr,hsup,hLI,hmod,hchi,hbin,ho,hi,hm,himage,hcomp,S,hS,hsource,hcase⟩

end CFSG.Quasithin.Chapter14.Section06
