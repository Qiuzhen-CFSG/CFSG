module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicCore
public import CFSG.Quasithin.Chapter14.Section06.SourceNormalSubgroups
public import CFSG.Quasithin.Chapter14.Section06.SourceIntersection
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.ResidualCentralizer
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Classification
public import Theory.GroupTheory.GeneralizedFitting.InnerMovingActor

/-!
# The normalizer of the paired residual centralizer

For the actual original C.5 configuration, D = (T ∩ I) ∩ C_G(O²(I)) is
normal in I. If D is nontrivial,14.6.9's normalizer control puts N_G(D)
in IStar with the same intersection with T. Original14.6.6 supplies that
intersection as a full Sylow, and14.6.7 supplies the vanishing odd core and
the marked involution. The complete1.1.5 classification then applies to
every ordinary component of this literal normalizer.

The final theorem produces such a marked ordinary component if the
normalizer is not of characteristic two. Neither minimality of N_G(D)
nor a factorization theorem is an input. The subsequent moved-block
embedding exclusion of1.2.8(2), needed to rule out this component, remains
a separate source step.

Source: Aschbacher--Smith14.6.9, printed p.1026;14.6.6--7 and1.1.5(3).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterC.Section05.BlockAnalysis
open Chapter15.Section03.Candidates.ComponentStructure
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

/-- Normalizer, Sylow and marked ordinary-component data for the literal
centralizer D in the original paired C.5 branch. Only IStar is used. -/
theorem source_paired_centralizer_normalizer_data
    (I Λ : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (hne : ((T : Subgroup G) ⊓ I) ⊓
      centralizer ((pResidual 2 I).map I.subtype : Set G) ≠ ⊥) :
    let R := (T : Subgroup G) ⊓ I
    let K := (pResidual 2 I).map I.subtype
    let D := R ⊓ centralizer (K : Set G)
    let ID := normalizer (D : Set G)
    I ≤ ID ∧
    ID ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M) ∧
    (T : Subgroup G) ⊓ ID = R ∧
    IsSQTK KnownSimple.IsKnownSimple ID ∧
    pPrimeCore 2 ID = ⊥ ∧
    generalizedFitting (ID ⊓ Mc : Subgroup G) = pCore 2 (ID ⊓ Mc : Subgroup G) ∧
    ∃ (S : Sylow 2 ID) (z : G),
      (S : Subgroup ID).map ID.subtype = R ∧ z ∈ centralInvolutions T ∧
      Chapter1.Lemma115Hypotheses ID S Mc z ∧
      ∀ A : Subgroup ID, IsComponent ID A →
        A.map ID.subtype = ⁅A.map ID.subtype, zpowers z⁆ ∧
        ¬ A.map ID.subtype ≤ Mc ∧ HasModelAction115 A z := by
  let R := (T : Subgroup G) ⊓ I
  let K := (pResidual 2 I).map I.subtype
  let D := R ⊓ centralizer (K : Set G)
  let ID := normalizer (D : Set G)
  have hID : I ≤ ID := c.sylow_centralizer_normalized
  obtain ⟨hstar,heq,_,_⟩ := source_lemma_14_6_9_normalizers T
    ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) M Mc I hI D hne inf_le_left hID
  obtain ⟨⟨S,hS⟩,_⟩ := source_suitable_intersection_sylow hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal ID hstar.1
  obtain ⟨⟨z,hz,h115⟩,hfit,hodd⟩ := source_lemma_14_6_7_initial hG T hempty hM
    hunique hmany hcard e hab H hH u hu ID hstar.1 S hS
  have hsqtk : IsSQTK KnownSimple.IsKnownSimple ID :=
    hG.twoLocal_sqtk ⟨D,hne,T.isPGroup'.to_le (inf_le_left.trans inf_le_left),rfl⟩
  refine ⟨hID,hstar,heq,hsqtk,hodd,hfit,S,z,hS.trans heq,hz,h115,?_⟩
  intro A hA
  exact Chapter1.lemma_1_1_5_three_of_local_classification hG
    (fun _ _ _ => ChapterA.Section02.theoremsABC_knownSimple)
    (fun _ _ _ _ _ _ d hm => d.classify hm) ID S Mc z h115 A hA

/-- Failure of characteristic two in N_G(D) produces an actual ordinary
component with the complete1.1.5 model/action conclusion. -/
theorem source_paired_centralizer_ordinary_component
    (I Λ : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (hne : ((T : Subgroup G) ⊓ I) ⊓
      centralizer ((pResidual 2 I).map I.subtype : Set G) ≠ ⊥)
    (hF : let ID := normalizer (((T : Subgroup G) ⊓ I) ⊓
      centralizer ((pResidual 2 I).map I.subtype : Set G) : Set G)
      generalizedFitting ID ≠ pCore 2 ID) :
    let R := (T : Subgroup G) ⊓ I
    let D := R ⊓ centralizer ((pResidual 2 I).map I.subtype : Set G)
    let ID := normalizer (D : Set G)
    ∃ (S : Sylow 2 ID) (z : G) (A : Subgroup ID),
      (S : Subgroup ID).map ID.subtype = R ∧ z ∈ centralInvolutions T ∧
      Chapter1.Lemma115Hypotheses ID S Mc z ∧ IsComponent ID A ∧
      A.map ID.subtype = ⁅A.map ID.subtype, zpowers z⁆ ∧
      ¬ A.map ID.subtype ≤ Mc ∧ HasModelAction115 A z := by
  obtain ⟨_,_,_,_,hodd,_,S,z,hS,hz,h115,hmarks⟩ :=
    source_paired_centralizer_normalizer_data hG T hempty hM hunique hmany hcard e hab H hH
      u hu hindex hmove hproduct hU3 hlocal I Λ hI c hne
  obtain ⟨A,hA⟩ := exists_component_of_oddCore_eq_bot hodd hF
  exact ⟨S,z,A,hS,hz,h115,hA,hmarks A hA⟩

end CFSG.Quasithin.Chapter14.Section06
