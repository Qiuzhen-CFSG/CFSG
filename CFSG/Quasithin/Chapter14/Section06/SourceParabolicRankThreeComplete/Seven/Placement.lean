module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.RankFiveNaturalSixPlacement.FixedCore

/-!
# The first-parabolic fixed vector in the ordinary seven-letter case

A nonzero vector fixed by the first residual excludes the larger Sylow
intersection T₀, since that intersection would force the residual to equal L
and contradict C_T(L)=1. Once the preferred-centralizer condition applies,
the central correction of this vector has an escaping centralizer, forcing
u into the original module by maximal intersection. The vector need not be
fixed by the entire generated group.

Source: Aschbacher--Smith, original14.6.10(5), pp.1029--1030.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.Seven
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem centralizer_mem_H_of_nontrivial_two_element
    {U : Subgroup G} (hU : IsPGroup 2 U) {v : G} (hv : v ∈ U) (hne : v ≠ 1) :
    centralizer ({v} : Set G) ∈ Chapter1.H G := by
  let A := zpowers v
  let C := centralizer ({v} : Set G)
  have hAC : A ≤ C := zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hCA : C ≤ normalizer (A : Set G) := by
    have he : centralizer (A : Set G) = C := by
      change centralizer (zpowers v : Set G) = centralizer ({v} : Set G)
      rw [zpowers_eq_closure,centralizer_closure]
    rw [← he]
    exact Subgroup.centralizer_le_normalizer _
  have hAp := hU.to_le (zpowers_le.mpr hv)
  have hcore := le_pCoreIn_of_normalizes hAp hAC hCA
  intro hz
  have hh : v ∈ (⊥ : Subgroup G) := hz ▸ hcore (mem_zpowers v)
  exact hne hh

private theorem residual_eq_of_sylow_index_two (T : Sylow 2 G) (L R S : Subgroup G)
    (hL : IsPPerfect 2 L) (hR : IsPPerfect 2 R)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hSR : S ≤ normalizer (R : Set G)) (hRL : R ≤ L)
    (hST : S ≤ (T : Subgroup G)) (hi : S.relIndex (T : Subgroup G) = 2)
    (hS : Chapter1.IsSylowIn 2 S (R ⊔ S))
    (eL : ((L ⊔ (T : Subgroup G) : Subgroup G) ⧸ pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) ≃*
      Equiv.Perm (Fin 3))
    (eR : ((R ⊔ S : Subgroup G) ⧸ pCore 2 (R ⊔ S : Subgroup G)) ≃* Equiv.Perm (Fin 3)) : R = L := by
  let J := L ⊔ (T : Subgroup G)
  let P := R ⊔ S
  have hPJ : P ≤ J := sup_le (hRL.trans le_sup_left) (hST.trans le_sup_right)
  have hTindex : (T : Subgroup G).relIndex J = 3 := by
    have hh := SymmetricThreeTwoCore.sylow_index_three eL (T.subtype le_sup_right)
    exact hh
  have hSindex : S.relIndex P = 3 := by
    obtain ⟨SP,hSP⟩ := hS
    have hh := SymmetricThreeTwoCore.sylow_index_three eR SP
    have he : S.subgroupOf P = (SP : Subgroup P) := by
      exact (congrArg (fun A : Subgroup G => A.subgroupOf P) hSP).symm.trans
        (comap_map_eq_self_of_injective P.subtype_injective _)
    change (S.subgroupOf P).index = 3
    rw [he]
    exact hh
  have hpi : P.relIndex J = 2 := by
    have h1 := relIndex_mul_relIndex S (T : Subgroup G) J hST le_sup_right
    have h2 := relIndex_mul_relIndex S P J le_sup_right hPJ
    rw [hi,hTindex] at h1
    rw [hSindex] at h2
    omega
  let PN := P.subgroupOf J
  let : PN.Normal := normal_of_index_eq_two hpi
  have hpq : IsPGroup 2 (J ⧸ PN) := IsPGroup.of_card (n := 1) (by
    change Nat.card (J ⧸ P.subgroupOf J) = 2^1
    rw [←index_eq_card]
    exact hpi)
  have hres : (pResidual 2 J).map J.subtype ≤ P := by
    rintro x ⟨j,hj,rfl⟩
    exact (show pResidual 2 J ≤ PN from sInf_le ⟨inferInstance,hpq⟩) hj
  have hr := embedded_pResidual_eq_of_le_of_residual_le 2 hPJ hres
  rw [embedded_pResidual_join_pGroup R S hR (T.isPGroup'.to_le hST) hSR,
    embedded_pResidual_join_pGroup L (T : Subgroup G) hL T.isPGroup' hTL] at hr
  exact hr


open Chapter12.Section08 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

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

/-- Fixation by the literal first residual suffices to force Tᵢ=Tᵤ.
No fixation by the whole generated group is assumed. -/
theorem source_sylow_eq_of_first_fixed_vector
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hout : ¬ I ⊓ M ≤ Mc)
    (hpreferred : (T : Subgroup G) ⊓ I = (T : Subgroup G) ⊓ centralizer ({u} : Set G) →
      I ≤ centralizer ({u} : Set G))
    (a : G) (ha : a ∈ conjugateSpanBy (localModule T M) H)
    (ha1 : a ≠ 1)
    (hRa : (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ≤ centralizer ({a} : Set G)) :
    (T : Subgroup G) ⊓ I = (T : Subgroup G) ⊓ centralizer ({u} : Set G) ∧
      I ≤ centralizer ({u} : Set G) := by
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  let L := sourceResidual M Mc
  let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
  let S := (T : Subgroup G) ⊓ I
  let Tu := (T : Subgroup G) ⊓ centralizer ({u} : Set G)
  let T0 := suitableQuotientCentralizer h u
  have hi := source_lemma_14_6_3_1 hG T hempty hM hunique hmany hcard e hab H hH
    u hu hindex hmove hproduct
  have hSTu : Tu ≤ S := le_inf inf_le_left hI.1.2.1
  have hS0 := source_suitable_intersection_le_quotientCentralizer hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1
  have hS : Chapter1.IsSylowIn 2 S I :=
    (source_suitable_intersection_sylow hG T hempty hM hunique hmany hcard e hab H hH
      u hu hindex hmove hproduct hU3 hlocal I hI.1).1
  have hRL : R ≤ L := (map_subtype_le _).trans inf_le_left
  have hRI : R ≤ I := (map_subtype_le _).trans inf_le_right
  have hRnormal : S ≤ normalizer (R : Set G) :=
    ((le_inf (inf_le_left.trans h.normalizes_L)
      (inf_le_right.trans I.le_normalizer)).trans inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image _ (pResidual 2 (L ⊓ I : Subgroup G)))
  have hnot : S ≠ T0 := by
    intro hST0
    have hSindex : S.relIndex (T : Subgroup G) = 2 := hST0 ▸ hindex
    have hcover := (source_lemma_14_6_6_3 hG T hempty hM hunique hmany hcard e hab H hH
      u hu hindex hmove hproduct I hI.1.2.1 hout).1
    obtain ⟨eR⟩ := (source_intersection_parabolic_data hG T hempty hM hunique hmany hcard e
      hab H hH u hu hindex hmove hproduct I hI.1.2.1 hS hcover).1
    obtain ⟨eL⟩ := (Section02.source_residualSylow_quotient hG T hempty hM hunique
      hmany hcard e).2
    have he : R = L := residual_eq_of_sylow_index_two T L R S
      ((pResidual_eq_top_iff 2 L).mp h.residual) (isPPerfect_embedded_pResidual 2 (L ⊓ I))
      h.normalizes_L hRnormal hRL inf_le_left hSindex
      (hS.restrict le_sup_right (sup_le hRI inf_le_right)) eL eR
    have haT : a ∈ (T : Subgroup G) := h.QH_le_T (h.UH_le_QH ha)
    have haL : a ∈ centralizer (L : Set G) := by
      intro l hl
      have hlR : l ∈ R := he.symm ▸ hl
      exact mem_centralizer_singleton_iff.mp (hRa hlR)
    have hz := source_residual_sylow_centralizer_eq_bot hG T hempty hM hunique hmany hcard e
    exact ha1 (show a ∈ (⊥ : Subgroup G) from hz ▸ ⟨haT,haL⟩)
  have hSTuEq : S = Tu := by
    have hm := relIndex_mul_relIndex Tu S T0 hSTu hS0
    have htwo : Tu.relIndex T0 = 2 := hi.1
    rw [htwo] at hm
    rcases (Nat.dvd_prime Nat.prime_two).mp (show Tu.relIndex S ∣ 2 from ⟨_,hm.symm⟩) with hs | hs
    · exact le_antisymm (relIndex_eq_one.mp hs) hSTu
    · have hz : S.relIndex T0 = 1 := by rw [hs] at hm; omega
      exact (hnot (le_antisymm hS0 (relIndex_eq_one.mp hz))).elim
  have hIu := hpreferred hSTuEq
  exact ⟨hSTuEq,hIu⟩

end CFSG.Quasithin.Chapter14.Section06.Seven

namespace CFSG.Quasithin.Chapter14.Section06.Seven
variable {G : Type*} [Group G] [Finite G]
variable {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)

/-- Central correction and maximal intersection place u in W when the
component centralizer of the chosen vector escapes both excluded groups.
Unlike the six-letter fixed-core lemma, the whole group need not fix a. -/
theorem involution_mem_of_escaping_vector_centralizer (u a : G)
    (hu : u ∈ D.UH) (ha : a ∈ D.UH) (ha1 : a ≠ 1)
    (W I C M Mc : Subgroup G) (haW : a ∈ W) (hCI : C ≤ I)
    (hI : I ∈ IStar (D.T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      (suitableCentralizer (D := D) u) Mc M))
    (hTI : (D.T : Subgroup G) ⊓ I = suitableCentralizer (D := D) u)
    (hTa : suitableCentralizer (D := D) u ≤ centralizer ({a} : Set G))
    (hIu : I ≤ centralizer ({u} : Set G))
    (hMc : ¬ C ⊓ centralizer ({a} : Set G) ≤ Mc)
    (hM : ¬ C ⊓ centralizer ({a} : Set G) ≤ M)
    (hi : (suitableCentralizer (D := D) u).relIndex (suitableQuotientCentralizer h u) = 2)
    (hgen : suitableQuotientCentralizer h u = D.QH ⊔ suitableCentralizer (D := D) u)
    (hmove : ¬ D.QH ≤ centralizer ({u} : Set G)) : u ∈ W := by
  by_contra huW
  have hTu0 : suitableCentralizer (D := D) u ≤ suitableQuotientCentralizer h u := by
    rw [hgen]
    exact le_sup_right
  have contradiction (v : G) (hv : v ∈ D.UH) (hne : v ≠ 1)
      (hCv : C ⊓ centralizer ({a} : Set G) ≤ centralizer ({v} : Set G))
      (h0v : suitableQuotientCentralizer h u ≤ centralizer ({v} : Set G)) : False := by
    have hJ : centralizer ({v} : Set G) ∈ outsideOvergroups (Chapter1.H G)
        (suitableCentralizer (D := D) u) Mc M :=
      ⟨centralizer_mem_H_of_nontrivial_two_element h.g2_hypothesis.U_isPGroup hv hne,
        hTu0.trans h0v,fun hh => hMc (hCv.trans hh),fun hh => hM (hCv.trans hh)⟩
    have he := (lemma14_6_4 hI hJ (hTI.symm ▸ hTu0.trans h0v)).2
    have h0Tu : suitableQuotientCentralizer h u ≤ suitableCentralizer (D := D) u := by
      rw [←hTI,←he]
      exact le_inf inf_le_left h0v
    have hi1 := relIndex_eq_one.mpr h0Tu
    omega
  rcases RankFiveNaturalSixPlacement.fixed_central_correction h u a hu ha hTa hi hgen hmove
      with hfix | hfix
  · exact contradiction a ha ha1 inf_le_right hfix
  · apply contradiction (a*u) (D.UH.mul_mem ha hu) ?_ ?_ hfix
    · intro hz
      have he : u = a⁻¹ := by
        calc u = a⁻¹ * (a*u) := by group
             _ = a⁻¹ := by rw [hz,mul_one]
      exact huW (he ▸ W.inv_mem haW)
    · intro t ht
      apply mem_centralizer_singleton_iff.mpr
      have hta := mem_centralizer_singleton_iff.mp ht.2
      have htu := mem_centralizer_singleton_iff.mp (hIu (hCI ht.1))
      calc
        t * (a*u) = (t*a)*u := (mul_assoc _ _ _).symm
        _ = (a*t)*u := congrArg (· * u) hta
        _ = a*(t*u) := mul_assoc _ _ _
        _ = a*(u*t) := congrArg (a * ·) htu
        _ = (a*u)*t := (mul_assoc _ _ _).symm

end CFSG.Quasithin.Chapter14.Section06.Seven
