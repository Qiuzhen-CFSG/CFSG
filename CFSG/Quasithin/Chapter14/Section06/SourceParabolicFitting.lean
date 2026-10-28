module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicQuotient
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.HighRankMarked
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicTriple
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRecognition
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.GeometricSourceAssembly
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.Mathieu.OuterNormalRank

/-!
# Characteristic two for the actual generated parabolics

If F*(I) differs from O₂(I), original 14.6.8 supplies a rank-four normal
elementary subgroup in the literal second parabolic modulo O₃′(I). Its
rank forces the marked Aut(M₁₂) amalgam. The original central involution
survives in that quotient parabolic, selecting the involution-centralizer
vertex; its normal elementary subgroups have rank at most three.

The final application constructs every parabolic and quotient from the
original suitable-involution setup. Only the two compatible marked
recognition inputs are retained; their source producers are the G₂
radius-two and Mathieu radius-three recognition modules.

Source: Aschbacher--Smith, original 14.6.10(4), printed p.1028.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
universe u
open ChapterF Chapter12.Section08 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type u} [Group G] [Finite G]

theorem source_parabolic_characteristic_two_of_marked_enumeration
    (hF1 : ChapterF.SourceAssembly.CharacteristicTwoMarkedAmalgamInput.{u})
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
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I)
    (I2 : Subgroup G) (hSI2 : (T : Subgroup G) ⊓ I ≤ I2)
    (hI2H : I2 ≤ H) (A : Subgroup I)
    (htriple : ChapterF.IsGoldschmidtTriple A (I2.subgroupOf I))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H))) :
    generalizedFitting I = pCore 2 I := by
  classical
  by_contra hF
  let q := QuotientGroup.mk' (pPrimeCore 3 I)
  let U := (conjugateSpanBy (localModule T M) H).subgroupOf I
  let B := I2.subgroupOf I
  let E := U.map q
  obtain ⟨hEB,hE,hEN,hEr⟩ := source_parabolic_quotient_elementary_rank
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI S hS
    I2 hSI2 hI2H A htriple hF hrank
  let : IsElementaryAbelian 2 E := hE
  let : IsElementaryAbelian 2 (E.subgroupOf (B.map q)) :=
    IsElementaryAbelian.subgroupOf hEB
  let : (E.subgroupOf (B.map q)).Normal := hEN
  have hc := source_parabolic_quotient_center_ne_bot hG T hempty hM hunique
    hmany hcard e hab H hH u hu I hI S hS I2 hSI2 hI2H A htriple hF
  have hq := goldschmidt_quotient_triple_of_elementary_rank htriple E hEr
  have hr : 4 ≤ primeRank 2 (I ⧸ pPrimeCore 3 I) :=
    hEr.trans (Theory.GroupTheory.primeRank_le_of_injective 2 E.subtype E.subtype_injective)
  have hmarked := hq.aut_mathieu_marked_of_high_rank hF1
    htriple.primeToThreeCore_quotient_twoCore_eq_bot hr
  have hbound : primeRank 2 (E.subgroupOf (B.map q)) ≤ 3 := by
    rcases hmarked with hm | hm
    · exact ChapterF.SourceAssembly.Mathieu.outer_centered_parabolic_normal_elementary_primeRank_le_three
        hm (B.map q) (Or.inr rfl) hc (E.subgroupOf (B.map q))
    · exact ChapterF.SourceAssembly.Mathieu.outer_centered_parabolic_normal_elementary_primeRank_le_three
        hm (B.map q) (Or.inl rfl) hc (E.subgroupOf (B.map q))
  rw [primeRank_equiv 2 (subgroupOfEquivOfLe hEB)] at hbound
  omega

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

theorem source_lemma_14_6_10_4_of_cover
    (hF1 : ChapterF.SourceAssembly.CharacteristicTwoMarkedAmalgamInput.{u})
    (I I2 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hSI2 : (T : Subgroup G) ⊓ I ≤ I2) (hI2H : I2 ≤ H)
    (hquot2 : Nonempty ((I2 ⧸ pCore 2 I2) ≃* Equiv.Perm (Fin 3)))
    (hcover : (sourceResidual M Mc : Set G) =
      ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
        (sourceResidual M Mc ⊓ I).subtype : Set G) *
          ((sourceResidual M Mc).pCoreIn 2 : Set G))
    (hgen : ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2 = I)
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H))) :
    generalizedFitting I = pCore 2 I := by
  have ht := source_parabolic_goldschmidtTriple hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct hU3 hlocal I I2 hI hSI2 hI2H hquot2 hcover hgen
  obtain ⟨S,hS⟩ := (source_suitable_intersection_sylow hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1).1
  exact source_parabolic_characteristic_two_of_marked_enumeration hF1 hG T hempty hM
    hunique hmany hcard e hab H hH u hu I hI S hS I2 hSI2 hI2H _ ht hrank

theorem source_lemma_14_6_10_4_of_escape
    (hF1 : ChapterF.SourceAssembly.CharacteristicTwoMarkedAmalgamInput.{u})
    (I I2 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hSI2 : (T : Subgroup G) ⊓ I ≤ I2) (hI2H : I2 ≤ H)
    (hquot2 : Nonempty ((I2 ⧸ pCore 2 I2) ≃* Equiv.Perm (Fin 3)))
    (hout : ¬ I ⊓ M ≤ Mc)
    (hgen : ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2 = I)
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H))) :
    generalizedFitting I = pCore 2 I := by
  have hcover := (source_lemma_14_6_6_3 hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct I hI.1.2.1 hout).1
  exact source_lemma_14_6_10_4_of_cover hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct hU3 hlocal hF1 I I2 hI hSI2 hI2H
    hquot2 hcover hgen hrank

theorem source_generated_parabolic_characteristic_two_of_marked_recognition
    (two : ChapterF.SourceAssembly.Goldschmidt.RadiusTwoMarkedInput.{u})
    (three : ChapterF.SourceAssembly.Goldschmidt.RadiusThreeMarkedInput.{u})
    (I H2 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hout : ¬ I ⊓ M ≤ Mc)
    (hSylH2 : Chapter1.IsSylowIn 2 (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u) H2)
    (hH2kernel : H2 ≤
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).kernel (zpowers u))
    (hH2quot : Nonempty ((H2 ⧸ pCore 2 H2) ≃* Equiv.Perm (Fin 3)))
    (hH2out : ¬ H2 ≤ M)
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H))) :
    let I2 := (pResidual 2 H2).map H2.subtype ⊔ ((T : Subgroup G) ⊓ I)
    let I0 := ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2
    generalizedFitting I0 = pCore 2 I0 := by
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  let L := sourceResidual M Mc
  let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
  let S := (T : Subgroup G) ⊓ I
  let I2 := (pResidual 2 H2).map H2.subtype ⊔ S
  let I0 := (R ⊔ S) ⊔ I2
  obtain ⟨hI0,hS,hgen,hI2H2,_⟩ := source_generated_parabolic_cores_of_marked_recognition
    hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
    two three I H2 hI hout hSylH2 hH2kernel hH2quot hH2out hcoreIndex hrank
  have hH2H : H2 ≤ H := fun x hx =>
    ((h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu))).mp (hH2kernel hx)).1
  have hSI2 : (T : Subgroup G) ⊓ I0 ≤ I2 := by
    rw [hS]
    exact le_sup_right
  have hS0 := source_suitable_intersection_le_quotientCentralizer hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1
  have hi := source_lemma_14_6_3_1 hG T hempty hM hunique hmany hcard e hab H hH
    u hu hindex hmove hproduct
  have hsecond := suitable_second_parabolic_data h u hu H2 S
    (le_inf inf_le_left hI.1.2.1) hS0 hi.1 hi.2.2.2.1
    hSylH2 hH2kernel hH2quot hlocal
  have hcover := (source_lemma_14_6_6_3 hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct I hI.1.2.1 hout).1
  have hSyl := (source_suitable_intersection_sylow hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1).1
  have hRout := (source_intersection_parabolic_data hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct I hI.1.2.1 hSyl hcover).2.2.2
  have hout0 : ¬ I0 ⊓ M ≤ Mc := by
    intro hh
    apply hRout
    exact (le_inf (le_sup_left.trans le_sup_left)
      (((map_subtype_le _).trans inf_le_left).trans (sourceResidual_le M Mc))).trans hh
  have hF1 := ChapterF.SourceAssembly.characteristicTwoMarked_of_large_nonabelian
    (ChapterF.SourceAssembly.Goldschmidt.largeNonabelian_of_marked_recognition two three)
  exact source_lemma_14_6_10_4_of_escape hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct hU3 hlocal hF1 I0 I2 hI0 hSI2
    (hI2H2.trans hH2H) hsecond.2.1 hout0 hgen hrank

end CFSG.Quasithin.Chapter14.Section06
