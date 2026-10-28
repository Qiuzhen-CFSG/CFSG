module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.Input
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.GoldschmidtSize.Complete
public import Theory.GroupTheory.DihedralEightSections
/-!
# Small Sylow subgroups in the original star component

Pass the actual Goldschmidt triple to its quotient by O₂(H). Every map
from a subgroup killing that subgroup's two-core factors through its
image in H/O₂(H). Gol80 therefore bounds Sylow two-subgroups of its image
by 128. Applying this to the original star action yields the bound on the
literal C.2.7 component; no marked model or Sylow bound is assumed.

Source: Aschbacher--Smith, 14.6.10(5), p.1029, comparing C.2.7 with F.6.18;
Goldschmidt (1980), Theorem A.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open ChapterF

variable {D E : Type*} [Group D] [Finite D] [Group E] [Finite E]

private theorem sylow_bound_of_twoCore_kernel
    {A B : Subgroup D} (h : IsGoldschmidtTriple A B)
    (K : Subgroup D) (f : K →* E) (hf : Function.Surjective f)
    (hk : pCore 2 K ≤ f.ker) (P : Sylow 2 E) : Nat.card P ≤ 128 := by
  let q := (QuotientGroup.mk' (pCore 2 D)).comp K.subtype
  have hq : q.ker ≤ f.ker := by
    apply le_trans (b := pCore 2 K) _ hk
    rw [show q.ker = (pCore 2 D).subgroupOf K by
      simp only [q,←MonoidHom.comap_ker,QuotientGroup.ker_mk']
      rfl]
    exact le_sSup ⟨inferInstance,pCore_isPGroup.comap_subtype⟩
  let e := QuotientGroup.quotientKerEquivRange q
  let r := (QuotientGroup.lift q.ker f hq).comp e.symm.toMonoidHom
  have hr : Function.Surjective r := by
    intro x
    obtain ⟨k,rfl⟩ := hf x
    refine ⟨e (QuotientGroup.mk' q.ker k),?_⟩
    change (QuotientGroup.lift q.ker f hq) (e.symm (e (QuotientGroup.mk' q.ker k))) = _
    rw [e.symm_apply_apply]
    rfl
  obtain ⟨S,hS⟩ := h.quotient_twoCore.intersection_sylow
  have hb : Nat.card S ≤ 128 := by
    rw [←hS]
    exact h.quotient_twoCore.intersection_card_le_128 h.quotient_twoCore_eq_bot
  exact (sylow_card_section_le S q.range r hr P).trans hb

open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

/-- The literal C.2.7 star component inherits the complete Gol80 bound. -/
theorem c27_star_sylow_card_le_128
    {G : Type*} [Group G] [Finite G] {H K R M : Subgroup G}
    (hi : Input KnownSimple.IsKnownSimple H R M K)
    {A B : Subgroup H} (ht : IsGoldschmidtTriple A B)
    (P : Sylow 2 (starImage K R K)) : Nat.card P ≤ 128 := by
  let e := subgroupOfEquivOfLe hi.component.1
  let f := (toStarImage K R).comp e.toMonoidHom
  have hf : Function.Surjective f := (toStarImage_surjective K R).comp e.surjective
  have hk : pCore 2 (K.subgroupOf H) ≤ f.ker := by
    intro x hx
    have he : e x ∈ pCore 2 K := by
      rw [←pCore_map_iso 2 e]
      exact mem_map_of_mem _ hx
    change toStarImage K R (e x) = 1
    exact core_le_toStarImage_ker hi.normalizes he
  exact sylow_bound_of_twoCore_kernel ht (K.subgroupOf H) f hf hk P

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


/-- The selected component satisfies the Gol80 Sylow bound on its actual star image. -/
theorem source_parabolic_c27_star_bound
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
      KernelConclusion K (I1.pCoreIn 2) ∧ OffenderConclusion K (I1.pCoreIn 2) ∧
      ∀ P : Sylow 2 (starImage K (I1.pCoreIn 2) K), Nat.card P ≤ 128 := by
  obtain ⟨K,hn,hi⟩ := source_parabolic_c27_input hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank
    I I2 hI hSI2 hI2H hquot2 hout hgen
  have ht := source_parabolic_goldschmidtTriple_of_escape hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I I2 hI hSI2 hI2H hquot2 hout hgen
  have hc := ChapterC.C27Source.kernel_offender_from_source hi
  exact ⟨K,hn,hi,hc.1,hc.2,c27_star_sylow_card_le_128 hi ht⟩

end CFSG.Quasithin.Chapter14.Section06
