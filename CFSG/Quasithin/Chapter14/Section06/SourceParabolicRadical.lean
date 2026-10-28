module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicCore
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.Setup
public import Theory.GroupTheory.SylowLocalCore
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
/-!
# The literal pushing-up setup in original 14.6.10(5)

The first parabolic contains the original Sylow intersection T_I. Hence
its two-core R₁ equals the two-core of its relative normalizer in I.
The source identity R₁ = T_I ∩ O₂(LT), together with
O₂(LT) = C_LT(V), identifies R₁ with T_I ∩ C_G(V). Since M∩I
normalizes V, the normal closure of R₁ inside M∩I stays in C_G(V),
and Sylow intersection proves that R₁ is Sylow in this closure.

Together with the characteristic-normalizer control and nontriviality
already proved in 14.6.10(1–2), this constructs exactly Hypothesis C.2.3
on the original I, R₁ and M∩I. It needs no component or C.2.7 conclusion.
The escaping-intersection application discharges the earlier residual
factorization by 14.6.6(3).

Source: Aschbacher–Smith, refs/quasithin.pdf, 14.6.10(5), printed p.1029.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem core_radical {I J : Subgroup G} (P : Sylow 2 I)
    (hJI : J ≤ I) (hPJ : (P : Subgroup I).map I.subtype ≤ J)
    (hne : J.pCoreIn 2 ≠ ⊥) : IsPRadical 2 ((J.pCoreIn 2).subgroupOf I) := by
  have hRI := (pCoreIn_le 2 J).trans hJI
  refine ⟨?_,?_⟩
  · intro hb
    apply hne
    simpa only [map_subgroupOf_eq_of_le hRI, Subgroup.map_bot] using
      congrArg (map I.subtype) hb
  · apply map_injective I.subtype_injective
    change ((normalizer ((J.pCoreIn 2).subgroupOf I : Set I)).pCoreIn 2).map I.subtype = _
    rw [map_pCoreIn_of_injective 2 _ I.subtype I.subtype_injective,
      ←subgroupOf_normalizer_eq hRI, subgroupOf_map_subtype]
    simpa only [inf_comm, map_subgroupOf_eq_of_le hRI] using
      pCoreIn_normalizer_eq_of_sylow_le P hJI hPJ

private theorem sylow_normalClosure_of_centralizer
    {I M R V : Subgroup G} (P : Sylow 2 I)
    (hMI : M ≤ I) (hPM : (P : Subgroup I).map I.subtype ≤ M)
    (hR : R = (P : Subgroup I).map I.subtype ⊓ centralizer (V : Set G))
    (hMV : M ≤ normalizer (V : Set G)) :
    Chapter1.IsSylowIn 2 R ((normalClosure (R.subgroupOf M : Set M)).map M.subtype) := by
  let N := normalClosure (R.subgroupOf M : Set M)
  let W := N.map M.subtype
  have hRM : R ≤ M := (hR.le.trans inf_le_left).trans hPM
  have hRW : R ≤ W := by
    have hh := map_mono (f := M.subtype) (le_normalClosure (H := R.subgroupOf M))
    simpa only [map_subgroupOf_eq_of_le hRM] using hh
  have hMW : M ≤ normalizer (W : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le N)).mp
    change (W.subgroupOf M).Normal
    rw [show W.subgroupOf M = N from comap_map_eq_self_of_injective M.subtype_injective N]
    infer_instance
  have hWC : W ≤ centralizer (V : Set G) := by
    let : ((centralizer (V : Set G)).subgroupOf M).Normal :=
      normal_subgroupOf_of_le_normalizer
        (hMV.trans (normalizer_le_normalizer_centralizer V))
    exact (map_le_iff_le_comap).mpr (normalClosure_le_normal
      (N := (centralizer (V : Set G)).subgroupOf M)
      (fun _ hr => (hR.le hr).2))
  obtain ⟨PM,hPM'⟩ := P.exists_map_subtype_eq_of_le hMI hPM
  obtain ⟨Q,hQ⟩ := PM.exists_map_subtype_eq_inf_of_normalizes (map_subtype_le N) hMW
  refine ⟨Q, hQ.trans ?_⟩
  rw [hPM']
  exact le_antisymm ((inf_le_inf_left _ hWC).trans hR.ge)
    (le_inf (hR.le.trans inf_le_left) hRW)

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter12.Section08 Chapter1.RadicalExclusions

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

/-- The original first parabolic satisfies C.2.3 in I with overgroup I∩M.
Only the preceding source factorization is retained as an input. -/
theorem source_parabolic_pushingUpSetup
    (I I2 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (hcover : (sourceResidual M Mc : Set G) =
      ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
        (sourceResidual M Mc ⊓ I).subtype : Set G) *
          ((sourceResidual M Mc).pCoreIn 2 : Set G))
    (hgen : ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2 = I) :
    let I1 := (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)
    PushingUpSetup KnownSimple.IsKnownSimple I (I1.pCoreIn 2) (I ⊓ M) := by
  let L := sourceResidual M Mc
  let S := (T : Subgroup G) ⊓ I
  let I1 := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype ⊔ S
  let R := I1.pCoreIn 2
  let V := localModule T M
  have hI1I : I1 ≤ I := sup_le ((map_subtype_le _).trans inf_le_right) inf_le_right
  have hRI : R ≤ I := (pCoreIn_le 2 I1).trans hI1I
  have hSyl := (source_suitable_intersection_sylow hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1).1
  have hdata := source_intersection_parabolic_data hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct I hI.1.2.1 hSyl hcover
  have hcontrol := source_lemma_14_6_10_1_2 hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I I2 hI
    hcoreIndex hrank hcover hgen
  have hR : R = S ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2 := hdata.2.2.1
  have hrankTwo := Section02.source_lemma_14_2_4 hG T hempty hM hunique hmany hcard e
  have hSC : R = S ⊓ centralizer (V : Set G) := by
    have hc : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
        (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
      simpa only [Section02.rankTwoSeed_eq_localModule] using hrankTwo.centralizer
    rw [hR, ←hc]
    exact le_antisymm (inf_le_inf_left _ inf_le_right)
      (le_inf inf_le_left (le_inf
        (inf_le_left.trans (inf_le_left.trans le_sup_right)) inf_le_right))
  have hSM : S ≤ I ⊓ M := le_inf inf_le_right (inf_le_left.trans hrankTwo.sylow_le)
  obtain ⟨P,hP⟩ := hSyl
  refine ⟨sqtk_of_mem_H hG hI.1.1,hRI,inf_le_left,?_,?_,?_⟩
  · exact core_radical P hI1I (hP.le.trans le_sup_right) hcontrol.2.1
  · have hc := characteristicNormalizerClosure_subgroupOf_le hRI hcontrol.1
    exact fun x hx => ⟨x.property,hc hx⟩
  · apply sylow_normalClosure_of_centralizer P inf_le_left (hP.le.trans hSM)
    · simpa only [hP] using hSC
    · have hn : M ≤ normalizer (V : Set G) := by
        simpa only [Section02.rankTwoSeed_eq_localModule] using
          (RankTwoHypothesis.M_normalizes_seed (T := T) (M := M))
      exact inf_le_right.trans hn

/-- The escaping-intersection source branch supplies the actual factorization
and hence every hypothesis of C.2.3 for the original first parabolic. -/
theorem source_parabolic_pushingUpSetup_of_escape
    (I I2 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (hout : ¬ I ⊓ M ≤ Mc)
    (hgen : ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2 = I) :
    let I1 := (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)
    PushingUpSetup KnownSimple.IsKnownSimple I (I1.pCoreIn 2) (I ⊓ M) := by
  have hcover := (source_lemma_14_6_6_3 hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct I hI.1.2.1 hout).1
  exact source_parabolic_pushingUpSetup hG T hempty hM hunique hmany hcard e hab
    H hH u hu hindex hmove hproduct hU3 hlocal I I2 hI hcoreIndex hrank hcover hgen

end CFSG.Quasithin.Chapter14.Section06
