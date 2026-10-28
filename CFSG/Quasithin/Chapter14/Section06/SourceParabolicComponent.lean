module
public import CFSG.Quasithin.Chapter14.Section06.SourceSolvableInvariantSubgroups
public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree.DistinctCores
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentReduction
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.Rigidity.Noncyclic
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# The original component choice after the solvable parabolic exclusions

The unequal original parabolic two-cores retain the Goldschmidt triple in
I/O₃′(I), with common Sylow larger than order two. If its three-core were
noncyclic, F.6.16 would produce one of the two marked solvable alternatives
already excluded on the original source group. Hence the three-core is
cyclic, and F.6.17 constructs a normal component containing one of the
literal quotient parabolic residuals and supplementing the other parabolic.

Source: Aschbacher--Smith, the opening component reduction in 14.6.10(5),
printed pp.1028--1029, using F.6.10 and F.6.16--17, pp.306,308--309.
The later C.2.7 block selection and rank-three conclusion remain separate.
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


/-- The original escaping parabolics give a quotient triple with cyclic three-core. -/
theorem source_parabolic_quotient_preparation
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
    IsGoldschmidtTriple ((I1.subgroupOf I).map q) ((I2.subgroupOf I).map q) ∧
      IsCyclic (pCore 3 (I ⧸ pPrimeCore 3 I)) := by
  let I1 := (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
    (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)
  let A := I1.subgroupOf I
  let B := I2.subgroupOf I
  have hI1I : I1 ≤ I := sup_le ((map_subtype_le _).trans inf_le_right) inf_le_right
  have hI2I : I2 ≤ I := le_sup_right.trans_eq hgen
  have ht := source_parabolic_goldschmidtTriple_of_escape hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I I2 hI hSI2 hI2H hquot2 hout hgen
  have hcover := (source_lemma_14_6_6_3 hG T hempty hM hunique hmany hcard e hab H hH
    u hu hindex hmove hproduct I hI.1.2.1 hout).1
  have hcores := (source_lemma_14_6_10_1_2 hG T hempty hM hunique hmany hcard e hab
    H hH u hu hindex hmove hproduct hU3 hlocal I I2 hI hcoreIndex hrank hcover hgen).2.2
  have hne : A.pCoreIn 2 ≠ B.pCoreIn 2 := by
    intro he
    apply hcores
    have hh := congrArg (Subgroup.map I.subtype) he
    simpa only [map_pCoreIn_of_injective 2 _ I.subtype I.subtype_injective,
      A,B,map_subgroupOf_eq_of_le hI1I,map_subgroupOf_eq_of_le hI2I] using hh
  have hqt := ht.quotient_primeToThreeCore_of_distinct_cores hne
  have hnot := ht.primeToThreeCore_intersection_not_cyclic_two hne
  have hsq : IsSQTK KnownSimple.IsKnownSimple I := by
    let N := normalizer (I.pCoreIn 2 : Set G)
    have hIN : I ≤ N := I.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
    have hN : IsTwoLocal N := ⟨I.pCoreIn 2,hI.1.1,isPGroup_pCoreIn 2 I,rfl⟩
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hIN)).mp
      ((hG.twoLocal_sqtk hN).subgroup (I.subgroupOf N))
  refine ⟨hqt,?_⟩
  by_contra hn
  have hm := ChapterF.SourceAssembly.source_marked_models hsq (MulEquiv.refl _)
    hqt hn hnot
  exact source_f618_marked_second_cases_exclusion hG T hempty hM hunique hmany hcard
    e hab H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank I hI B ht hm

/-- F.6.17 now chooses a normal component with the literal quotient residual marking. -/
theorem source_parabolic_quotient_component
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
    ∃ K : Subgroup (I ⧸ pPrimeCore 3 I), IsComponent (I ⧸ pPrimeCore 3 I) K ∧
      K.Normal ∧ ¬ K ≤ pCore 3 (I ⧸ pPrimeCore 3 I) ∧
      (((pResidual 2 A).map A.subtype ≤ K ∧ K ⊔ B = ⊤) ∨
        ((pResidual 2 B).map B.subtype ≤ K ∧ K ⊔ A = ⊤)) := by
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
  exact ChapterF.SourceAssembly.cyclic_component_reduction
    ChapterA.Section02.theoremA_knownSimple hsq (MulEquiv.refl _) ht hc

/-- The normal quotient component lifts to a genuine normal C-component of the original I. -/
theorem source_parabolic_normal_cComponent
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
    ∃ K : Subgroup I, K.IsCComponent ∧ K.Normal ∧
      IsComponent (I ⧸ pPrimeCore 3 I) (K.map (QuotientGroup.mk' (pPrimeCore 3 I))) := by
  have ht := source_parabolic_goldschmidtTriple_of_escape hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I I2 hI hSI2 hI2H hquot2 hout hgen
  let : Group.IsSolvable (pPrimeCore 3 I) := ht.primeToThreeCore_solvable
  obtain ⟨K,hK,hn,_⟩ := source_parabolic_quotient_component hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank
    I I2 hI hSI2 hI2H hquot2 hout hgen
  obtain ⟨L,hL,he⟩ := hK.isCComponent.exists_map_quotient_eq (pPrimeCore 3 I)
  exact ⟨L,hL,cComponent_normal_of_quotient_normal hL (pPrimeCore 3 I) (he.symm ▸ hn),
    he.symm ▸ hK⟩

end CFSG.Quasithin.Chapter14.Section06
