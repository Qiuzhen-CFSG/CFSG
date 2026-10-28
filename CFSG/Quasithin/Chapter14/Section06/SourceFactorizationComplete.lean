module
public import CFSG.Quasithin.Chapter14.Section06.SourceCharacteristicTwoFactorization
public import CFSG.Quasithin.Chapter14.Section06.SourceFactorizationReduction
public import CFSG.Quasithin.Chapter14.Section06.SourceOrderBound

/-!
# Original 14.6.9 and its invariant-subgroup consumers

The characteristic-two paired-block contradiction and the noncharacteristic
component-rank contradiction give both residual products for minimal outside
choices. The inclusion-minimal reduction lifts these products to every
maximal-intersection choice. The original order bound completes 14.6.9.

The literal products also discharge the factorization premises in original
14.6.10(3) and its normal-complement exclusion. No component, block, geometry
or factorization callback remains in these source conclusions.

Source: Aschbacher--Smith 14.6.9--10, printed pp.1025--1029.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
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
variable
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))

include hcoreIndex hrank

/-- Both residual products at the original inclusion-minimal choice. -/
theorem source_minimal_factorizations
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)) :
    (let L := sourceResidual M Mc
     let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
     (L : Set G) = (R : Set G) * (L.pCoreIn 2 : Set G) ∧
       (L ⊔ (T : Subgroup G) : Subgroup G) =
         (R : Set G) * ((T : Subgroup G) ⊓ I : Subgroup G) *
           ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) := by
  by_cases hf : generalizedFitting I = pCore 2 I
  · exact source_characteristicTwo_factorization hG T hempty hM hunique hmany hcard e hab H hH u hu
      hindex hmove hproduct hU3 hlocal hcoreIndex hrank I hf hI
  · exact source_noncharacteristic_factorization hG T hempty hM hunique hmany hcard e hab H hH u hu
      hindex hmove hproduct hU3 hlocal hrank I hf hI

/-- Both literal original residual products for every maximal-intersection choice. -/
theorem source_factorizations
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)) :
    (let L := sourceResidual M Mc
     let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
     (L : Set G) = (R : Set G) * (L.pCoreIn 2 : Set G) ∧
       (L ⊔ (T : Subgroup G) : Subgroup G) =
         (R : Set G) * ((T : Subgroup G) ⊓ I : Subgroup G) *
           ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) := by
  apply source_factorizations_of_characteristic_minimal hG T hempty hM hunique hmany hcard e hab H hH u hu
    hindex hmove hproduct hU3 hlocal hcoreIndex hrank _ I hI
  intro hindex' J hJ hf
  exact source_characteristicTwo_factorization hG T hempty hM hunique hmany hcard e hab H hH u hu
    hindex hmove hproduct hU3 hlocal hindex' hrank J hf hJ

/-- Original 14.6.9: the Sylow order bound and the full residual product. -/
theorem source_lemma_14_6_9
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)) :
    2 ^ 11 < Nat.card T ∧
      (sourceResidual M Mc ⊔ (T : Subgroup G) : Subgroup G) =
        ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
          (sourceResidual M Mc ⊓ I).subtype : Set G) *
          ((T : Subgroup G) ⊓ I : Subgroup G) *
          ((sourceResidual M Mc ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) := by
  exact ⟨(source_lemma_14_6_9_order hG T hempty hM hunique hmany hcard e hab H hH
    hcoreIndex hrank).2, (source_factorizations hG T hempty hM hunique hmany hcard e hab H hH u hu
    hindex hmove hproduct hU3 hlocal hcoreIndex hrank I hI).2⟩

/-- Original 14.6.10(3), with all factorization premises discharged. -/
theorem source_lemma_14_6_10_3
    (I P : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hPI : P ≤ I)
    (hN : (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I) ≤
        normalizer (P : Set G)) :
    (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ≤ P ∨
        P ≤ M ⊓ centralizer (localModule T M : Set G) := by
  apply source_lemma_14_6_10_3_of_factorizations hG T hempty hM hunique hmany hcard e hab
    H hH u hu hindex hmove hproduct hU3 hlocal I P hI _ hPI hN
  intro J _ hJ
  exact (source_factorizations hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank J hJ).1

/-- The original normal-complement contradiction from the proved products. -/
theorem source_normal_complement_exclusion
    (I P : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hPI : P ≤ I) (hN : I ≤ normalizer (P : Set G))
    (hgen : P ⊔ ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) = I)
    (hmeet : P ⊓ sourceResidual M Mc ≤ (sourceResidual M Mc).pCoreIn 2) : False := by
  apply source_normal_complement_exclusion_of_factorizations hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I P hI _ hPI hN hgen hmeet
  intro J _ hJ
  exact (source_factorizations hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank J hJ).1

end CFSG.Quasithin.Chapter14.Section06
