module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedTrivialCentralizer
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedCentralizerTrivial
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedCentralizerCharacteristicTwo
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicNaturalBlockExclusion

/-!
# The characteristic-two branch of original 14.6.9

For the original paired A₅ configuration, the centralizer-normalizer source
has characteristic two. Its two-core contains the original paired core,
forcing the residual centralizer to be trivial. The proved quotient-section
argument then excludes the paired configuration. Together with the natural
and small-block exclusions, this gives both original residual products for
an inclusion-minimal characteristic-two choice.

No normalizer, component, coordinate, geometry or factorization premise is
retained beyond the original source hypotheses.

Source: Aschbacher--Smith 14.6.9, printed pp.1025--1027.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
/-- The full original paired configuration is impossible. -/
theorem source_paired_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
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
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5)
    (hpairIndex : (((T : Subgroup G) ⊓ I).relIndex Λ) = 2)
    (hΛT : Λ ≤ (T : Subgroup G)) : False := by
  have hD := source_paired_centralizer_trivial_of_characteristicTwo
    hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
      I Λ hI c b i j hij hs hi hpairIndex
      (fun hne => source_paired_centralizer_characteristicTwo
        hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
          I Λ hI.1 c b i j hij hs hi hne)
  exact source_paired_exclusion_of_trivial_centralizer
    hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
      I hI Λ c b i j hij hs hi hpairIndex hΛT hD

/-- Both original residual products in the characteristic-two minimal branch. -/
theorem source_characteristicTwo_factorization
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
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
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (I : Subgroup G) (hf : generalizedFitting I = pCore 2 I)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)) :
    (let L := sourceResidual M Mc
     let LI := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
     (L : Set G) = (LI : Set G) * (L.pCoreIn 2 : Set G) ∧
       (L ⊔ (T : Subgroup G) : Subgroup G) =
         (LI : Set G) * ((T : Subgroup G) ⊓ I : Subgroup G) *
           ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) := by
  rcases source_characteristicTwo_paired_or_factorization
    hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
      hcoreIndex hrank I hf hI with
    ⟨Λ,hΛ,hiΛ,c,_,_,b,i,j,hij,hs,hi,_⟩ | hfactor
  · exact (source_paired_exclusion
      hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
        I hI Λ c b i j hij hs hi hiΛ hΛ).elim
  · exact hfactor

end CFSG.Quasithin.Chapter14.Section06
