module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.F618ChiZeroSource
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.PlaneMovement
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleResidual
public import Theory.GroupTheory.PResidual.PrimeToQuotientLift
/-!
# Residual generation by the original parabolic component

The Goldschmidt triple has the same two-residual and prime-to-three residual.
Modulo the prime-to-three core, F.6.17 identifies its two-residual with the
quasisimple generalized Fitting subgroup already selected by C.2.7/F.6.18.
Equality lifts through the coprime kernel, retaining the same component K.
Thus K = O²(I), the original Sylow intersection supplements K, and the
first parabolic residual lies in K. The original model and quotient marks
are retained together in the conclusion.

Source: Aschbacher--Smith 14.6.10(5), printed p.1029, after exclusion of the
F.6.18 product row. Compatible block reconstruction remains a later step.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06
universe u
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open ChapterF SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type u} [Group G] [Finite G]

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

private theorem component_eq_residual
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
    ∀ (K : Subgroup I), K.IsCComponent → K.Normal →
      K.map (QuotientGroup.mk' (pPrimeCore 3 I)) = generalizedFitting (I ⧸ pPrimeCore 3 I) →
      IsQuasisimple (generalizedFitting (I ⧸ pPrimeCore 3 I)) → K = pResidual 2 I := by
  intro K hK hn hmap hqfit
  have hresq := And.intro hmap hqfit
  let : K.Normal := hn
  let : Group.IsPerfect K := hK.perfect
  have ht := source_parabolic_goldschmidtTriple_of_escape hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I I2 hI hSI2 hI2H hquot2 hout hgen
  let q := QuotientGroup.mk' (pPrimeCore 3 I)
  let D := I ⧸ pPrimeCore 3 I
  have hsq : IsSQTK KnownSimple.IsKnownSimple I := by
    let N := normalizer (I.pCoreIn 2 : Set G)
    have hIN : I ≤ N := I.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
    have hN : IsTwoLocal N := ⟨I.pCoreIn 2,hI.1.1,isPGroup_pCoreIn 2 I,rfl⟩
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hIN)).mp
      ((hG.twoLocal_sqtk hN).subgroup (I.subgroupOf N))
  have hquot := source_parabolic_quotient_f618 hG T hempty hM hunique hmany hcard e hab H hH u hu
    hindex hmove hproduct hU3 hlocal hcoreIndex hrank I I2 hI hSI2 hI2H hquot2 hout hgen
  have hDtriple := hquot.1
  have hfD : pResidual 2 D = generalizedFitting D := by
    apply ChapterF.SourceAssembly.twoResidual_eq_fitting_of_quasisimple_fitting
      (ChapterA.Section02.theoremA_knownSimple)
      (fun L _ _ => ChapterA.Section02.theoremC_knownSimple)
      hsq (MulEquiv.refl D) hDtriple
    · exact hquot.2.1
    · exact hresq.2
  have hqd : K.map q = pResidual 2 D := by
    simpa only [q,D] using hresq.1.trans hfD.symm
  have hthreeD : pResidual 2 D = primeToResidual 3 D :=
    ChapterF.IsGoldschmidtTriple.twoResidual_eq_primeToThreeResidual (G := D) hDtriple
  have hqthree : K.map q = primeToResidual 3 D := hqd.trans hthreeD
  have htwoI : pResidual 2 I = primeToResidual 3 I :=
    ChapterF.IsGoldschmidtTriple.twoResidual_eq_primeToThreeResidual ht
  have hKperf : IsPPerfect 2 K := by
    intro N hN hqN
    let : N.Normal := hN
    by_contra hne
    let : Nontrivial (K ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (K ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (K ⧸ N) := hqN.isNilpotent
    exact Group.IsPerfect.not_isSolvable (K ⧸ N) inferInstance
  have hKres : K ≤ pResidual 2 I := le_pResidual_of_isPPerfect K hKperf
  have hKprime : K ≤ primeToResidual 3 I := htwoI ▸ hKres
  have heq := eq_primeToResidual_of_coprime_quotient_image 3
    (pPrimeCore 3 I) K pPrimeCore_coprime_card hKprime hqthree
  exact heq.trans htwoI.symm

/-- The actual selected component is the whole residual, supplemented by the source Sylow. -/
theorem source_parabolic_residual_data
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
  obtain ⟨K,hK,hn,hfit,hq,hchi,hbin,ho,hi,hm,himage,hcomp,S,hS,hsource,hcase⟩ :=
    source_parabolic_f618_c27_not_chiZero hG T hempty hM hunique hmany hcard e hab H hH u hu
      hindex hmove hproduct hU3 hlocal hcoreIndex hrank I I2 hI hSI2 hI2H hquot2 hout hgen
  have hKr : K = pResidual 2 I := component_eq_residual hG T hempty hM hunique hmany hcard
    e hab H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank I I2 hI hSI2
    hI2H hquot2 hout hgen K hK hn hcase.1 hcase.2
  have hsup : K.map I.subtype ⊔ ((T : Subgroup G) ⊓ I) = I := by
    rw [hKr]
    obtain ⟨P,hP⟩ := (source_suitable_intersection_sylow hG T hempty hM hunique hmany
      hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1).1
    exact embedded_pResidual_sup_of_common_sylow I _ P hP
  have hLI : (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ≤ K.map I.subtype := by
    rw [hKr]
    exact embedded_pResidual_mono 2 inf_le_right
  exact ⟨K,hK,hn,hfit,hq,hKr,hsup,hLI,hchi,hbin,ho,hi,hm,himage,hcomp,S,hS,hsource,hcase⟩

end CFSG.Quasithin.Chapter14.Section06
