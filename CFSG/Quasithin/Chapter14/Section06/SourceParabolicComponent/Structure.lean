module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicFitting.Complete
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRadical
public import Theory.GroupTheory.GeneralizedFitting.PrimeCoreNormalized

/-!
# The original parabolic component of characteristic two

The selected normal C-component inherits characteristic two from the original
parabolic group. Its literal image modulo the prime-to-three core is retained
for the component quotient calculation in the following source step.

Source: Aschbacher--Smith 14.6.10(4--5), printed pp.1028--1029.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open ChapterF SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

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


/-- The original selected component is normal and has characteristic two. -/
theorem source_parabolic_characteristic_two_cComponent
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
    ∃ K : Subgroup I, K.IsCComponent ∧ K.Normal ∧ generalizedFitting K = pCore 2 K ∧
      IsComponent (I ⧸ pPrimeCore 3 I) (K.map (QuotientGroup.mk' (pPrimeCore 3 I))) := by
  obtain ⟨K,hK,hn,himage⟩ := source_parabolic_normal_cComponent hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank
    I I2 hI hSI2 hI2H hquot2 hout hgen
  let : K.Normal := hn
  have hF1 := ChapterF.SourceAssembly.characteristicTwoMarked_of_large_nonabelian
    (ChapterF.SourceAssembly.Goldschmidt.largeNonabelian_of_marked_recognition
      ChapterF.SourceAssembly.Goldschmidt.radiusTwoMarkedInput
      ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree.radiusThreeMarkedInput)
  have hfit := source_lemma_14_6_10_4_of_escape hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct hU3 hlocal hF1 I I2 hI hSI2 hI2H
    hquot2 hout hgen hrank
  exact ⟨K,hK,hn,generalizedFitting_eq_pCore_of_normalized_by_pCore K hfit
    (by rw [normalizer_eq_top]; exact le_top),himage⟩

/-- The original C.2.3 setup and normal characteristic-two component are constructed together. -/
theorem source_parabolic_component_preparation
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
    Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple I (I1.pCoreIn 2) (I ⊓ M) ∧
    ∃ K : Subgroup I, K.IsCComponent ∧ K.Normal ∧ generalizedFitting K = pCore 2 K ∧
      IsComponent (I ⧸ pPrimeCore 3 I) (K.map (QuotientGroup.mk' (pPrimeCore 3 I))) := by
  exact ⟨source_parabolic_pushingUpSetup_of_escape hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I I2 hI hcoreIndex hrank hout hgen,
    source_parabolic_characteristic_two_cComponent hG T hempty hM hunique hmany
      hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank
      I I2 hI hSI2 hI2H hquot2 hout hgen⟩

end CFSG.Quasithin.Chapter14.Section06
