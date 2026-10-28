module
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.BlockKernel
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.KnownSimple
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
import Mathlib.Tactic
/-!
# The C.2.12 normalizer equality

The actual section centralizer lies in M by the complete known-simple C.1.29
outside-block theorem. Frattini factorization over that centralizer then puts
the whole normalizer of M0 in M. This proves C.2.12 from the genuine C.2.8
configuration, with no preselected component or local classification row.

Source: Aschbacher–Smith, C.2.12, printed p.148.
-/
public section
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Subgroup Theory.GroupTheory ChapterA.Section04
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]
variable {H M L R V : Subgroup G}

/-- The actual section centralizer lies in M: otherwise unconditional C.1.29
supplies a chi-block excluded by the source perfect-action calculation. -/
theorem section_le_local (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V) :
    twoSectionCentralizer (conjugateSpanBy L M) H ≤ M := by
  let X := twoSectionCentralizer (conjugateSpanBy L M) H
  have hRH := h.radical_le.trans h.local_le
  have hXH : X ≤ H := twoSectionCentralizer_le _ _
  let f : X →* H := inclusion hXH
  have hX : IsSQTK KnownSimple.IsKnownSimple X :=
    ⟨h.sqtk.stronglyQuasithin.of_injective f (inclusion_injective hXH),
      h.sqtk.isKGroup.of_injective f (inclusion_injective hXH)⟩
  obtain ⟨S,hS⟩ := h.section_sylow_in_H
  have hRX : R ≤ X := hS ▸ map_subtype_le _
  have hSR : (S : Subgroup X) = R.subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le hRX]
  have hmap : (R.subgroupOf X).map f = R.subgroupOf H := by
    ext x
    constructor
    · rintro ⟨r,hr,rfl⟩
      exact hr
    · intro hr
      exact ⟨⟨x,hRX hr⟩,hr,rfl⟩
  have hcontrol : (S : Subgroup X).characteristicNormalizerClosure ≤ M.subgroupOf X := by
    rw [hSR]
    have hc := map_characteristicNormalizerClosure_le f (inclusion_injective hXH) (R.subgroupOf X)
    rw [hmap] at hc
    intro x hx
    exact h.characteristic_control (hc (mem_map_of_mem f hx))
  by_contra hnot
  have hproper : M.subgroupOf X ≠ ⊤ := fun he => hnot (subgroupOf_eq_top.mp he)
  obtain ⟨K,hout,hK,_⟩ := RankOne.ChiProduct.SelectedRankOne.outside_moved_chi_knownSimple
    hX h.section_fitting_eq_core S (M.subgroupOf X) hcontrol hproper
  exact hout (h.section_chi_le_local K hK)

private theorem frattini_factorization {C N : Subgroup G} (hCN : C ≤ N)
    (hNC : N ≤ normalizer (C : Set G)) (S : Sylow 2 C) :
    (N : Set G) = (C : Set G) *
      ((N ⊓ normalizer ((S : Subgroup C).map C.subtype : Set G)) : Set G) := by
  let C' := C.subgroupOf N
  let : C'.Normal := (normal_subgroupOf_iff_le_normalizer hCN).mpr hNC
  let e : C ≃* C' := (subgroupOfEquivOfLe hCN).symm
  let S' : Sylow 2 C' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hmap : ((S' : Subgroup C').map C'.subtype).map N.subtype =
      (S : Subgroup C).map C.subtype := by
    change (((S : Subgroup C).map e.toMonoidHom).map C'.subtype).map N.subtype = _
    rw [map_map,map_map]
    rfl
  have hfr : C' ⊔ normalizer ((S' : Subgroup C').map C'.subtype : Set N) = ⊤ := by
    rw [sup_comm]
    exact S'.normalizer_sup_eq_top
  apply Set.Subset.antisymm
  · intro n hn
    have hn' : (⟨n,hn⟩ : N) ∈ C' ⊔ normalizer ((S' : Subgroup C').map C'.subtype : Set N) := by
      rw [hfr]; trivial
    obtain ⟨c,hc,k,hk,he⟩ := mem_sup_of_normal_left.mp hn'
    refine ⟨c,hc,k,⟨k.property,?_⟩,congrArg Subtype.val he⟩
    have hh := ((S' : Subgroup C').map C'.subtype).le_normalizer_map N.subtype
      (mem_map_of_mem N.subtype hk)
    rwa [hmap] at hh
  · rintro _ ⟨c,hc,k,hk,rfl⟩
    exact N.mul_mem (hCN hc) hk.1

/-- Full C.2.12 for the genuine full known-simple C.2.8 hypothesis. -/
theorem normalizer_span_eq (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V) :
    H ⊓ normalizer (conjugateSpanBy L M : Set G) = M := by
  let C := twoSectionCentralizer (conjugateSpanBy L M) H
  let N := H ⊓ normalizer (conjugateSpanBy L M : Set G)
  have hCN : C ≤ N := le_inf (twoSectionCentralizer_le _ _) (twoSectionCentralizer_le_normalizer _ _)
  obtain ⟨S,hS⟩ := h.section_sylow_in_H
  have he := frattini_factorization hCN (normalizer_twoSectionCentralizer _ _) S
  rw [hS] at he
  apply le_antisymm ?_ (le_inf h.local_le (le_normalizer_conjugateSpanBy L M))
  intro n hn
  obtain ⟨c,hc,k,hk,rfl⟩ := he ▸ (show n ∈ (N : Set G) from hn)
  exact M.mul_mem (h.section_le_local hc) (h.normalizer_le ⟨hk.1.1,hk.2⟩)
end CFSG.Quasithin.ChapterC.HypothesisC28
