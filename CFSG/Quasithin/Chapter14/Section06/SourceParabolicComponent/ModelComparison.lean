module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.F618Models
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.Models
/-!
# Comparing the two actual component images

The selected internal component K is used in both source classifiers.
Transport through its inclusion constructs C.2.7 Input; the actual
Goldschmidt triple bounds the Sylow order of its star image. Both this
image and its image in I/O₃′(I) are nontrivial quotients of the same
quasisimple K/O₂(K), so their central quotients are canonically isomorphic.
The comparison retains its formula on every original k in K.

The final source theorem combines the seven bounded B.5 models with the
marked F.6.18 alternatives and the product-or-generalized-Fitting split,
without independently choosing a second component.

Source: Aschbacher--Smith 14.6.10(5), printed p.1029. The further catalogue
intersection and compatible module/parabolic reconstruction remain separate.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

theorem c27_star_threePrime_central_quotient
    {I R M : Subgroup G} (K : Subgroup I) (hK : K.IsCComponent) [K.Normal]
    (hi : Input KnownSimple.IsKnownSimple I R M (K.map I.subtype))
    (himage : IsComponent (I ⧸ pPrimeCore 3 I)
      (K.map (QuotientGroup.mk' (pPrimeCore 3 I)))) :
    let C := K.map I.subtype
    let q := QuotientGroup.mk' (pPrimeCore 3 I)
    let a := K.equivMapOfInjective I.subtype I.subtype_injective
    ∃ e : (starImage C R C ⧸ center (starImage C R C)) ≃*
        ((K.map q) ⧸ center (K.map q)),
      ∀ k : K, e (QuotientGroup.mk' (center (starImage C R C))
          (toStarImage C R (a k))) =
        QuotientGroup.mk' (center (K.map q)) (q.subgroupMap K k) := by
  let C := K.map I.subtype
  let a := K.equivMapOfInjective I.subtype I.subtype_injective
  let b : (K ⧸ pCore 2 K) ≃* (C ⧸ pCore 2 C) :=
    QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let : (C.subgroupOf I).Normal := by
    change ((K.map I.subtype).comap I.subtype).Normal
    rw [comap_map_eq_self_of_injective I.subtype_injective K]
    infer_instance
  let : IsQuasisimple (C ⧸ pCore 2 C) := hi.quasisimple
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv b.symm
  let : IsQuasisimple (starImage C R C) := (ChapterC.C27Source.star_fitting_quasisimple hi).2
  let : IsSimpleGroup (starImage C R C ⧸ center (starImage C R C)) := IsQuasisimple.simple
  let : Nontrivial (starImage C R C) := (QuotientGroup.mk'_surjective (center _)).nontrivial
  let : IsQuasisimple (K.map (QuotientGroup.mk' (pPrimeCore 3 I))) := himage.2
  let : IsSimpleGroup ((K.map (QuotientGroup.mk' (pPrimeCore 3 I))) ⧸
      center (K.map (QuotientGroup.mk' (pPrimeCore 3 I)))) := IsQuasisimple.simple
  let : Nontrivial (K.map (QuotientGroup.mk' (pPrimeCore 3 I))) :=
    (QuotientGroup.mk'_surjective (center _)).nontrivial
  let f := (coreToStar hi.normalizes).comp b.toMonoidHom
  have hf : Function.Surjective f := (coreToStar_surjective hi.normalizes).comp b.surjective
  let g := twoCoreToThreePrimeImage K hK.subnormal
  have hg : Function.Surjective g := twoCoreToThreePrimeImage_surjective K hK.subnormal
  refine ⟨IsQuasisimple.imageCentralQuotientEquiv f hf g hg, ?_⟩
  intro k
  exact IsQuasisimple.imageCentralQuotientEquiv_mk f hf g hg (QuotientGroup.mk' (pCore 2 K) k)



omit [Finite G] in
private theorem comparison_input_of_internal_component
    {I R M : Subgroup G} (hs : Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple I R M)
    (K : Subgroup I) (hc : K.IsCComponent) [K.Normal]
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : generalizedFitting K = pCore 2 K)
    (ho : ¬ K.map I.subtype ≤ M) :
    Input KnownSimple.IsKnownSimple I R M (K.map I.subtype) := by
  let e := K.equivMapOfInjective I.subtype I.subtype_injective
  have he : (K.map I.subtype).subgroupOf I = K :=
    comap_map_eq_self_of_injective I.subtype_injective K
  have hq' : IsQuasisimple ((K.map I.subtype) ⧸ pCore 2 (K.map I.subtype)) := by
    let : IsQuasisimple (K ⧸ pCore 2 K) := hq
    exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  have hf' : generalizedFitting (K.map I.subtype) = pCore 2 (K.map I.subtype) := by
    rw [← map_generalizedFitting_equiv e, hf, pCore_map_iso]
  have hn : I ≤ normalizer (K.map I.subtype : Set G) := by
    have h := K.le_normalizer_map I.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
    exact h
  exact ⟨hs,⟨map_subtype_le K,he.symm ▸ hc⟩,hq',hf',ho,hs.radical_le.trans hn⟩


open scoped Pointwise
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
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



/-- The original C.2.7 and F.6.18 catalogues compare the same selected component. -/
theorem source_parabolic_f618_c27_comparison
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
        ((∃ r : FSource.ProductRow S, K.map q = r.first ∧ ¬ ChapterC.IsChiZeroBlock K) ∨
          (K.map q = generalizedFitting (I ⧸ pPrimeCore 3 I) ∧
            IsQuasisimple (generalizedFitting (I ⧸ pPrimeCore 3 I)))) := by
  obtain ⟨K,hK,hn,hfit,hq,ho,himage,_,S,hS,hsource,hcase⟩ :=
    source_parabolic_f618_component hG T hempty hM hunique hmany hcard e hab H hH u hu
      hindex hmove hproduct hU3 hlocal hcoreIndex hrank I I2 hI hSI2 hI2H hquot2 hout hgen
  let : K.Normal := hn
  have hs := source_parabolic_pushingUpSetup_of_escape hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I I2 hI hcoreIndex hrank hout hgen
  have hi := comparison_input_of_internal_component hs K hK hq hfit ho
  let : ((K.map I.subtype).subgroupOf I).Normal := by
    change ((K.map I.subtype).comap I.subtype).Normal
    rw [comap_map_eq_self_of_injective I.subtype_injective K]
    infer_instance
  have ht := source_parabolic_goldschmidtTriple_of_escape hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I I2 hI hSI2 hI2H hquot2 hout hgen
  have hm := ChapterC.C27Source.star_small_model_from_source hi (c27_star_sylow_card_le_128 hi ht)
  exact ⟨K,hK,hn,hfit,hq,ho,hi,hm,himage,
    c27_star_threePrime_central_quotient K hK hi himage,S,hS,hsource,hcase⟩

end CFSG.Quasithin.Chapter14.Section06
