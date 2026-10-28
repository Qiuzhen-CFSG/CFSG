module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.AlternatingSixMovedSource
public import Theory.Representation.BinaryOffender.IrreducibleMovedTransport
/-!
# Noncentral invariant subgroups of the actual A₆ moved module

The B.5 natural A₆ quotient makes the literal moved star module Irr⁺.
Thus an invariant subgroup inside it either centralizes the component or
is the whole moved module. This identifies the original noncentral plane
span, including the nonsplit five-dimensional augmentation case.

Source: Aschbacher–Smith B.5.1 and C.2.7, used in 14.6.10(5), p.1029.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {H K R M : Subgroup G}

/-- Irr⁺ identifies every noncentral invariant subgroup of the moved module. -/
theorem star_alternatingSix_moved_eq_of_source
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (e : starImage K R K ≃* alternatingGroup (Fin 6))
    (U : Subgroup (K ⊔ R : Subgroup G))
    (hU : U ≤ ⁅starV K R,K.subgroupOf (K ⊔ R)⁆)
    (hKU : K.subgroupOf (K ⊔ R) ≤ normalizer (U : Set (K ⊔ R : Subgroup G)))
    (hne : ¬ U ≤ centralizer (K.subgroupOf (K ⊔ R) : Set (K ⊔ R : Subgroup G))) :
    U = ⁅starV K R,K.subgroupOf (K ⊔ R)⁆ := by
  let V := starV K R
  let C := K.subgroupOf (K ⊔ R)
  let q := QuotientGroup.mk' (starKernel K R)
  let ρ := starRepresentation K R
  let J := offenderSubgroup ρ
  obtain ⟨hCJ,⟨c⟩⟩ := star_moved_section_from_source h
  obtain ⟨hi,_⟩ := AlternatingSixMovedModel.source_natural _ c
    ((subgroupOfEquivOfLe hCJ).trans e)
  let W := NormalElementaryQuotient.subspace V (U.subgroupOf V)
  have hUV : U ≤ V := hU.trans (commutator_le_left _ _)
  have hs : c.sectionData.space.toSubmodule =
      NormalElementaryQuotient.commutatorSpace V C := by
    rw [NormalElementaryQuotient.commutatorSpace_eq V q (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _),c.sectionData.space_eq]
    change subspaceCommutator (ρ.comp J.subtype) ⊤ ((starImage K R K).subgroupOf J) = _
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hCJ]
    rfl
  have hstab : (starImage K R K).subgroupOf J ≤ subspaceStabilizer (ρ.comp J.subtype) W := by
    intro a ha
    obtain ⟨b,hb,he⟩ := (show (a : StarQuotient K R) ∈ C.map q from ha)
    change (∀ v, ρ (a : StarQuotient K R) v ∈ W ↔ v ∈ W)
    rw [←he]
    have hst := NormalElementaryQuotient.stabilizer_comap V q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) (U.subgroupOf V)
    have hbN : b ∈ normalizer ((U.subgroupOf V).map V.subtype : Set (K ⊔ R : Subgroup G)) := by
      rw [map_subgroupOf_eq_of_le hUV]
      exact hKU hb
    rw [←hst] at hbN
    exact hbN
  have hWle : W ≤ c.sectionData.space.toSubmodule := by
    rw [hs]
    intro v hv
    exact hU hv
  rcases hi.eq_or_le_fixedSpace _ hstab hWle with heq | hfix
  · apply le_antisymm hU
    intro x hx
    let v : Additive V := Additive.ofMul ⟨x,commutator_le_left V C hx⟩
    have hv : v ∈ c.sectionData.space.toSubmodule := by
      rw [hs]
      exact hx
    rw [←heq] at hv
    exact hv
  · apply False.elim
    apply hne
    intro x hx
    let v : Additive V := Additive.ofMul ⟨x,hUV hx⟩
    have hf : v ∈ fixedSpace ρ (C.map q) := by
      intro a
      have ha : (⟨a,hCJ a.property⟩ : J) ∈ (starImage K R K).subgroupOf J := a.property
      exact hfix (show v ∈ W from hx) ⟨⟨a,hCJ a.property⟩,ha⟩
    exact (NormalElementaryQuotient.mem_fixedSpace_image V q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) C v).mp hf
/-- The same identification in the original ambient group, with literal maps. -/
theorem star_alternatingSix_moved_eq_of_source_ambient
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (e : starImage K R K ≃* alternatingGroup (Fin 6))
    (U : Subgroup G)
    (hU : U ≤ (⁅starV K R,K.subgroupOf (K ⊔ R)⁆).map
      (K ⊔ R : Subgroup G).subtype)
    (hKU : K ≤ normalizer (U : Set G))
    (hne : ¬ U ≤ centralizer (K : Set G)) :
    U = (⁅starV K R,K.subgroupOf (K ⊔ R)⁆).map
      (K ⊔ R : Subgroup G).subtype := by
  let J := K ⊔ R
  have hUJ : U ≤ J := hU.trans (map_subtype_le _)
  have hle : U.subgroupOf J ≤ ⁅starV K R,K.subgroupOf J⁆ := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hU hx
    have : y = x := Subtype.ext he
    exact this ▸ hy
  have hnorm : K.subgroupOf J ≤ normalizer (U.subgroupOf J : Set J) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro y
    exact (mem_normalizer_iff.mp (hKU hx)) y
  have hnon : ¬ U.subgroupOf J ≤ centralizer (K.subgroupOf J : Set J) := by
    intro hh
    apply hne
    intro x hx k hk
    have hc := hh (show (⟨x,hUJ hx⟩ : J) ∈ U.subgroupOf J from hx)
      ⟨k,mem_sup_left hk⟩ hk
    exact congrArg Subtype.val hc
  have he := star_alternatingSix_moved_eq_of_source h e (U.subgroupOf J) hle hnorm hnon
  have hm := congrArg (fun P : Subgroup J => P.map J.subtype) he
  rwa [map_subgroupOf_eq_of_le hUJ] at hm
end CFSG.Quasithin.ChapterC.C27Source
