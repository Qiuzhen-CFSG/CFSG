module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedOddRank
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedOrdinaryCentralization

/-!
# Characteristic two for the paired residual-centralizer normalizer

The moved deleted blocks centralize every ordinary component of N(D).
The known-simple odd-rank argument then excludes those components entirely.
Together with the source odd-core vanishing, this gives F*(N(D))=O₂(N(D))
under the original suitable-intersection and paired-block hypotheses.

Source: Aschbacher--Smith 14.6.9, printed p.1026.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section06
open Subgroup Theory.GroupTheory
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterC ChapterC.Section05.BlockAnalysis
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


/-- The literal normalizer of the paired residual centralizer is of characteristic two. -/
theorem source_paired_centralizer_characteristicTwo
    (I Λ : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5)
    (hne : ((T : Subgroup G) ⊓ I) ⊓
      centralizer ((pResidual 2 I).map I.subtype : Set G) ≠ ⊥) :
    let ID := normalizer (((T : Subgroup G) ⊓ I) ⊓
      centralizer ((pResidual 2 I).map I.subtype : Set G) : Set G)
    generalizedFitting ID = pCore 2 ID := by
  obtain ⟨_,_,_,hSQ,_,_,S,z,hS,_,_,hmodels⟩ :=
    source_paired_centralizer_normalizer_data hG T hempty hM hunique hmany hcard e hab H hH
      u hu hindex hmove hproduct hU3 hlocal I Λ hI c hne
  apply source_paired_centralizer_characteristicTwo_of_component_centralization
    hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
    I Λ hI c b i j hij hs hi hne
  dsimp only
  intro A hA
  obtain ⟨α,_,hm⟩ := (hmodels A hA).2.2
  exact source_paired_residual_centralizes_ordinary T I Λ c b i j hij hs hi S hS hSQ A hA ⟨α,hm⟩
end CFSG.Quasithin.Chapter14.Section06
