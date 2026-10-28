module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.F618ChiZero
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleResidual
/-!
# The original source component is not a chi-zero block

The quasisimple generalized Fitting subgroup of the actual prime-to-three
quotient equals its two-residual. Thus its quotient is a two-group, which
discharges the only extra premise of the full chi-zero row comparison.
The selected K, C.2.7 input and canonical central quotient comparison are
retained from the original construction.

Source: Aschbacher--Smith 14.6.10(5), printed p.1029.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open ChapterC.C27Source
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
namespace F618ChiZero

/-- The actual SQTK cover and Goldschmidt triple discharge the two-quotient
premise, leaving no rank or representation assumption. -/
theorem not_chiZero_of_source {J : Type*} [Group J] [Finite J]
    (hsq : IsSQTK KnownSimple.IsKnownSimple J)
    (K : Subgroup J) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hi : IsComponent (J ⧸ pPrimeCore 3 J) (K.map (QuotientGroup.mk' (pPrimeCore 3 J))))
    (heq : K.map (QuotientGroup.mk' (pPrimeCore 3 J)) =
      generalizedFitting (J ⧸ pPrimeCore 3 J))
    (hf : IsQuasisimple (generalizedFitting (J ⧸ pPrimeCore 3 J)))
    {A C : Subgroup (J ⧸ pPrimeCore 3 J)} {S : Sylow 2 (J ⧸ pPrimeCore 3 J)}
    (ht : ChapterF.IsGoldschmidtTriple A C)
    (hc : IsCyclic (pCore 3 (J ⧸ pPrimeCore 3 J)))
    (hsource : FSource.SourceAlternative A C S) : ¬ ChapterC.IsChiZeroBlock K := by
  have hr := ChapterF.SourceAssembly.twoResidual_eq_fitting_of_quasisimple_fitting
    ChapterA.Section02.theoremA_knownSimple
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    hsq (MulEquiv.refl _) ht hc hf
  have hquot : IsPGroup 2 ((J ⧸ pPrimeCore 3 J) ⧸
      generalizedFitting (J ⧸ pPrimeCore 3 J)) := by
    exact (isPGroup_quotient_pResidual 2).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hr)
  exact not_chiZero_of_two_quotient K hK hq hi heq hsource hquot

/-- In the actual source quotient, the original K/O₂(K) has no binary SL₂ model. -/
theorem not_binary_quotient_of_source {J : Type*} [Group J] [Finite J]
    (hsq : IsSQTK KnownSimple.IsKnownSimple J)
    (K : Subgroup J) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hi : IsComponent (J ⧸ pPrimeCore 3 J) (K.map (QuotientGroup.mk' (pPrimeCore 3 J))))
    (heq : K.map (QuotientGroup.mk' (pPrimeCore 3 J)) =
      generalizedFitting (J ⧸ pPrimeCore 3 J))
    (hf : IsQuasisimple (generalizedFitting (J ⧸ pPrimeCore 3 J)))
    {A C : Subgroup (J ⧸ pPrimeCore 3 J)} {S : Sylow 2 (J ⧸ pPrimeCore 3 J)}
    (ht : ChapterF.IsGoldschmidtTriple A C)
    (hc : IsCyclic (pCore 3 (J ⧸ pPrimeCore 3 J)))
    (hsource : FSource.SourceAlternative A C S)
    (B : BinaryField) (b : (K ⧸ pCore 2 K) ≃* SL(2,B.Carrier)) : False := by
  have hr := ChapterF.SourceAssembly.twoResidual_eq_fitting_of_quasisimple_fitting
    ChapterA.Section02.theoremA_knownSimple
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    hsq (MulEquiv.refl _) ht hc hf
  have hquot : IsPGroup 2 ((J ⧸ pPrimeCore 3 J) ⧸
      generalizedFitting (J ⧸ pPrimeCore 3 J)) := by
    exact (isPGroup_quotient_pResidual 2).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hr)
  exact not_binary_quotient_of_two_quotient K hK hq hi heq hsource hquot B b

end F618ChiZero

open scoped Pointwise
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




/-- The same selected source component is not a chi-zero block. -/
theorem source_parabolic_f618_c27_not_chiZero
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
      ¬ ChapterC.IsChiZeroBlock K ∧
      (∀ B : BinaryField, ¬ Nonempty ((K ⧸ pCore 2 K) ≃* SL(2,B.Carrier))) ∧
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
  obtain ⟨K,hK,hn,hfit,hq,ho,hi,hm,himage,hcomp,S,hS,hsource,hcase⟩ :=
    source_parabolic_f618_c27_fitting hG T hempty hM hunique hmany hcard e hab H hH u hu
      hindex hmove hproduct hU3 hlocal hcoreIndex hrank I I2 hI hSI2 hI2H hquot2 hout hgen
  obtain ⟨ht,hc⟩ := source_parabolic_quotient_preparation hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank
    I I2 hI hSI2 hI2H hquot2 hout hgen
  have hsq : IsSQTK KnownSimple.IsKnownSimple I := by
    let N := normalizer (I.pCoreIn 2 : Set G)
    have hIN : I ≤ N := I.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
    have hN : IsTwoLocal N := ⟨I.pCoreIn 2,hI.1.1,isPGroup_pCoreIn 2 I,rfl⟩
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hIN)).mp
      ((hG.twoLocal_sqtk hN).subgroup (I.subgroupOf N))
  refine ⟨K,hK,hn,hfit,hq,?_,?_,ho,hi,hm,himage,hcomp,S,hS,hsource,hcase⟩
  · exact hsource.elim
      (F618ChiZero.not_chiZero_of_source hsq K hK hq himage hcase.1 hcase.2 ht hc)
      (F618ChiZero.not_chiZero_of_source hsq K hK hq himage hcase.1 hcase.2 ht.symm hc)
  · rintro B ⟨b⟩
    exact hsource.elim
      (fun hs => F618ChiZero.not_binary_quotient_of_source hsq K hK hq himage
        hcase.1 hcase.2 ht hc hs B b)
      (fun hs => F618ChiZero.not_binary_quotient_of_source hsq K hK hq himage
        hcase.1 hcase.2 ht.symm hc hs B b)

end CFSG.Quasithin.Chapter14.Section06
