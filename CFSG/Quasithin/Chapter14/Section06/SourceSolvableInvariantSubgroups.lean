module
public import CFSG.Quasithin.Chapter14.Section06.SourceSolvableFactorization
public import CFSG.Quasithin.Chapter14.Section06.SourceInvariantSubgroups
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicTriple
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SecondCaseSupplement

/-!
# Excluding the solvable alternatives in original 14.6.10(5)

The two alternatives in F.6.18(2) make the generated group solvable. The
solvable specialization of 14.6.9 therefore supplies every factorization
used by the invariant-subgroup dichotomy. The model's normal supplement
misses the first cubic residual, so that dichotomy places it in C_M(V).
It and the first parabolic then generate a subgroup of M, contradicting
the outside choice. The final theorem constructs the literal Goldschmidt
triple in the escaping-intersection branch and excludes the unmarked row.

Source: Aschbacher–Smith, 14.6.10(3),(5), printed pp.1028–1029.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section06
open Subgroup Theory.GroupTheory
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem normal_supplement_residual_le (P S : Subgroup G)
    (hn : S ≤ normalizer (P : Set G)) (hp : IsPGroup 2 S) :
    (pResidual 2 (P ⊔ S : Subgroup G)).map (P ⊔ S).subtype ≤ P := by
  let J := P ⊔ S
  let : (P.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer (sup_le P.le_normalizer hn)
  have hq : IsPGroup 2 (J ⧸ P.subgroupOf J) :=
    isPGroup_quotient_of_sup_eq_top (P.subgroupOf J) (S.subgroupOf J)
      hp.comap_subtype (by rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self])
  have hr : pResidual 2 J ≤ P.subgroupOf J := sInf_le ⟨inferInstance,hq⟩
  rintro x ⟨a,ha,rfl⟩
  exact hr ha

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

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


theorem solvable_source_normal_supplement_exclusion
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (I P : Subgroup G) [Group.IsSolvable I]
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hPI : P ≤ I) (hN : I ≤ normalizer (P : Set G))
    (hgen : P ⊔ ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) = I)
    (hmiss : ¬ (pResidual 2 (((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) : Subgroup G)).map
        (((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I))).subtype ≤ P) : False := by
  have hfactor (J : Subgroup G) (hJI : J ≤ I)
      (hJ : J ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
        ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)) := by
    let : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective
      (f := inclusion hJI) (inclusion_injective _)
    exact source_lemma_14_6_9_of_solvable hG T hempty hM hunique hmany hcard e hab H hH
      u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank J hJ
  let R := (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
    (sourceResidual M Mc ⊓ I).subtype
  let S := (T : Subgroup G) ⊓ I
  have hRI : R ≤ I := (map_subtype_le _).trans inf_le_right
  have hS : S ≤ I := inf_le_right
  rcases source_lemma_14_6_10_3_of_factorizations hG T hempty hM hunique hmany hcard
    e hab H hH u hu hindex hmove hproduct hU3 hlocal I P hI hfactor hPI
      ((sup_le hRI hS).trans hN) with hRP | hPM
  · apply hmiss
    exact (embedded_pResidual_mono 2 (sup_le_sup hRP (le_refl S))).trans
      (normal_supplement_residual_le P S (hS.trans hN) (T.isPGroup'.to_le inf_le_left))
  · apply hI.1.2.2.2
    rw [←hgen]
    exact sup_le (hPM.trans inf_le_left) (sup_le
      (((map_subtype_le _).trans inf_le_left).trans (sourceResidual_le M Mc))
      (inf_le_left.trans hM.1.2))

open ChapterF ChapterF.SourceAssembly ChapterF.Noncyclic.MarkedRecognition
open MarkedCubicRecognition

theorem source_f618_marked_second_cases_exclusion
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (B : Subgroup I)
    (htriple : IsGoldschmidtTriple
      (((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
        (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)).subgroupOf I) B)
    (hm : let A := ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
        (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)).subgroupOf I
      let q := QuotientGroup.mk' (pPrimeCore 3 I)
      Nonempty (MarkedModel (A.map q) (B.map q) Nine nineAction
        (MonoidHom.inl C3 C3).range (MonoidHom.inr C3 C3).range) ∨
      Nonempty (MarkedModel (A.map q) (B.map q) (HeisenbergPrime 3) heisenbergAction
        leftAxis.range rightAxis.range)) : False := by
  let I1 := (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
    (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)
  let A := I1.subgroupOf I
  let q := QuotientGroup.mk' (pPrimeCore 3 I)
  have hI1I : I1 ≤ I := sup_le ((map_subtype_le _).trans inf_le_right) inf_le_right
  have hA : A.map I.subtype = I1 := map_subgroupOf_eq_of_le hI1I
  have hmodels : Nonempty ((I ⧸ pPrimeCore 3 I) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
      Nonempty ((I ⧸ pPrimeCore 3 I) ≃* HeisenbergExtension) := by
    rcases hm with hm | hm
    · obtain ⟨m⟩ := hm
      obtain ⟨ee⟩ := nineExtension_equiv_symmetric_product
      exact Or.inl ⟨m.ambientEquiv.symm.trans ee⟩
    · obtain ⟨m⟩ := hm
      exact Or.inr ⟨m.ambientEquiv.symm⟩
  let : Group.IsSolvable I := second_case_models_solvable htriple hmodels
  obtain ⟨P,hPn,hgen,hmiss⟩ := marked_second_cases_normal_supplement hm
  let : P.Normal := hPn
  obtain ⟨_,hgen',hmiss'⟩ := normal_supplement_preimage q
    (QuotientGroup.mk'_surjective _) A P hgen hmiss
  let P0 := (P.comap q).map I.subtype
  have hP0I : P0 ≤ I := map_subtype_le _
  have hN : I ≤ normalizer (P0 : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer hP0I).mp
    change (((P.comap q).map I.subtype).subgroupOf I).Normal
    rw [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective]
    infer_instance
  have hgen0 : P0 ⊔ I1 = I := by
    have hh := congrArg (Subgroup.map I.subtype) hgen'
    simpa only [Subgroup.map_sup,hA,←MonoidHom.range_eq_map,range_subtype] using hh
  have hmiss0 : ¬ (pResidual 2 I1).map I1.subtype ≤ P0 := by
    intro hh
    apply hmiss'
    apply (map_le_map_iff_of_injective I.subtype_injective).mp
    rw [map_embedded_pResidual,hA]
    exact hh
  exact solvable_source_normal_supplement_exclusion hG T hempty hM hunique hmany hcard
    e hab H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank I P0 hI
    hP0I hN hgen0 hmiss0
end CFSG.Quasithin.Chapter14.Section06


namespace CFSG.Quasithin.Chapter14.Section06
open Subgroup Theory.GroupTheory ChapterF
variable {G : Type*} [Group G] [Finite G]
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

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

theorem source_f618_second_case_exclusion
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (B : Subgroup I)
    (htriple : IsGoldschmidtTriple
      (((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
        (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)).subgroupOf I) B)
    (hm : Nonempty ((I ⧸ pPrimeCore 3 I) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
      ∃ N : Subgroup (I ⧸ pPrimeCore 3 I), ∃ _ : N.Normal,
        IsExtraspecial 3 N ∧ Nat.card N = 27 ∧ Monoid.exponent N = 3 ∧
        Nonempty (((I ⧸ pPrimeCore 3 I) ⧸ N) ≃* MarkedCubicRecognition.Four)) : False := by
  have hsq : IsSQTK KnownSimple.IsKnownSimple I := by
    let N := normalizer (I.pCoreIn 2 : Set G)
    have hIN : I ≤ N := I.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
    have hN : IsTwoLocal N := ⟨I.pCoreIn 2,hI.1.1,isPGroup_pCoreIn 2 I,rfl⟩
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hIN)).mp
      ((hG.twoLocal_sqtk hN).subgroup (I.subgroupOf N))
  exact source_f618_marked_second_cases_exclusion hG T hempty hM hunique hmany hcard
    e hab H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank I hI B htriple
    (ChapterF.SourceAssembly.marked_second_case_of_unmarked hsq htriple hm)

end CFSG.Quasithin.Chapter14.Section06

namespace CFSG.Quasithin.Chapter14.Section06
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

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

theorem source_generated_f618_second_case_exclusion
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
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2 = I)
    (hm : Nonempty ((I ⧸ pPrimeCore 3 I) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
      ∃ N : Subgroup (I ⧸ pPrimeCore 3 I), ∃ _ : N.Normal,
        IsExtraspecial 3 N ∧ Nat.card N = 27 ∧ Monoid.exponent N = 3 ∧
        Nonempty (((I ⧸ pPrimeCore 3 I) ⧸ N) ≃* MarkedCubicRecognition.Four)) : False := by
  have ht := source_parabolic_goldschmidtTriple_of_escape hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I I2 hI hSI2 hI2H hquot2 hout hgen
  exact source_f618_second_case_exclusion hG T hempty hM hunique hmany hcard e hab
    H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank I hI (I2.subgroupOf I) ht hm

end CFSG.Quasithin.Chapter14.Section06
