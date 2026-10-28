module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.Quotient
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.SolvableKernel
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.OriginalRestriction

/-!
# The genuine C.2.7 input for the original parabolic group

The source radical setup, normal component of characteristic two,
quasisimple two-core quotient, and escape from the local subgroup are
constructed for the same original I. Transport through its inclusion
therefore supplies the literal C.2.7 input and its proved kernel/offender
conclusions, with no remaining source-classification premise.

Source: Aschbacher--Smith 14.6.10(5), printed p.1029, applying
C.2.7(1--2), printed p.146. The later model and rank-three clauses are separate.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open ChapterF SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem source_c27_input_of_internal_component
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


/-- All local C.2.7 premises for the actual selected component are discharged. -/
theorem source_parabolic_c27_input
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
    ∃ K : Subgroup G, (K.subgroupOf I).Normal ∧
      Input KnownSimple.IsKnownSimple I (I1.pCoreIn 2) (I ⊓ M) K := by
  obtain ⟨hs,K,hK,hn,hfit,himage⟩ := source_parabolic_component_preparation hG T hempty
    hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
    hcoreIndex hrank I I2 hI hSI2 hI2H hquot2 hout hgen
  let : K.Normal := hn
  have hq := source_parabolic_component_twoCore_quasisimple hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
    I I2 hI hSI2 hI2H hquot2 hout hgen K hK himage
  have ho := source_parabolic_component_outside hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank
    I I2 hI hSI2 hI2H hquot2 hout hgen K hK himage
  refine ⟨K.map I.subtype,?_,source_c27_input_of_internal_component hs K hK hq hfit ho⟩
  change ((K.map I.subtype).comap I.subtype).Normal
  rw [comap_map_eq_self_of_injective I.subtype_injective K]
  infer_instance

/-- The kernel and offender clauses of C.2.7 for the original parabolic group. -/
theorem source_parabolic_c27_local_conclusions
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
    ∃ K : Subgroup G, (K.subgroupOf I).Normal ∧
      Input KnownSimple.IsKnownSimple I (I1.pCoreIn 2) (I ⊓ M) K ∧
      KernelConclusion K (I1.pCoreIn 2) ∧ OffenderConclusion K (I1.pCoreIn 2) := by
  obtain ⟨K,hn,hi⟩ := source_parabolic_c27_input hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank
    I I2 hI hSI2 hI2H hquot2 hout hgen
  exact ⟨K,hn,hi,ChapterC.C27Source.kernel_offender_from_source hi⟩

end CFSG.Quasithin.Chapter14.Section06
