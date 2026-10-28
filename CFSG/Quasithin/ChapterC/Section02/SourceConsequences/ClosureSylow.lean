module
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.Restriction
public import CFSG.Quasithin.ChapterC.Defs
import Mathlib.Tactic
/-!
# The normal-closure Sylow condition in C.2.10

The section centralizer of M0 is normal in M and contains R. Thus the
M-normal closure of R stays inside that centralizer. Maximality of the
original Sylow subgroup shows that the same R is Sylow in this closure.
This is the normal-closure clause of the genuine C.2.3 input.

Source: Aschbacher–Smith, C.2.10(4), printed p.147.
-/
public section
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Subgroup Theory.GroupTheory ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H M L R V : Subgroup G}

omit [Finite G] in
/-- C.2.10(4): the same actual R is Sylow in its normal closure inside M. -/
theorem sylow_in_normalClosure (h : HypothesisC28 κ H M L R V) :
    IsSylowInNormalClosure R M := by
  let X := conjugateSpanBy L M
  let C := twoSectionCentralizer X M
  have hCM : C ≤ M := twoSectionCentralizer_le _ _
  have hMC : M ≤ normalizer (C : Set G) :=
    (le_inf le_rfl (le_normalizer_conjugateSpanBy L M)).trans
      (normalizer_twoSectionCentralizer X M)
  let : (C.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hCM).mpr hMC
  obtain ⟨S,hS⟩ := h.section_sylow
  have hRC : R ≤ C := hS ▸ map_subtype_le _
  let N := normalClosure (R.subgroupOf M : Set M)
  have hNC : N ≤ C.subgroupOf M := normalClosure_le_normal (fun r hr => hRC hr)
  have hRN : R.subgroupOf M ≤ N := subset_normalClosure
  let f : N →* G := M.subtype.comp N.subtype
  have hRimage : R ≤ N.map M.subtype := by
    intro r hr
    exact ⟨⟨r,h.radical_le hr⟩,hRN hr,rfl⟩
  have hp : IsPGroup 2 ((R.subgroupOf M).subgroupOf N) :=
    h.radical_isTwoGroup.comap_subtype.comap_subtype
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  let Q := (P : Subgroup N).map f
  have hRQ : R ≤ Q := by
    intro r hr
    exact ⟨⟨⟨r,h.radical_le hr⟩,hRN hr⟩,hP hr,rfl⟩
  have hQC : Q ≤ C := by
    rintro q ⟨y,hy,rfl⟩
    exact hNC y.property
  have hSP : (S : Subgroup C) ≤ Q.subgroupOf C := by
    intro s hs
    exact hRQ (hS ▸ mem_map_of_mem C.subtype hs)
  have he := S.is_maximal' ((P.isPGroup'.map f).comap_subtype) hSP
  have hQR : Q ≤ R := by
    intro q hq
    have hs : (⟨q,hQC hq⟩ : C) ∈ (S : Subgroup C) := he ▸ hq
    exact hS ▸ mem_map_of_mem C.subtype hs
  refine ⟨P,?_⟩
  rw [map_map]
  exact le_antisymm hQR hRQ
end CFSG.Quasithin.ChapterC.HypothesisC28
