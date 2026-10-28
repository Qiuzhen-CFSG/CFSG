module

public import Theory.GroupTheory.ElementaryThompsonRelative
public import Mathlib.GroupTheory.Nilpotent

/-!
# Normalizer growth detected by an elementary Thompson subgroup

If the elementary Thompson subgroup of a Sylow subgroup of B is E, then
normalizers of that Sylow subgroup normalize E. A larger ambient p-group
supplies an element outside B by the normalizer condition, since the
intersection with B is still the original Sylow subgroup.

This supplies the strict module-normalizer growth in the original Rudvalis
unitary row. Source: Aschbacher--Smith 4.2.13, printed pp.611--612.
-/

public section
open Subgroup Stellmacher
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A Sylow subgroup that is not ambient Sylow forces strict growth of the
normalizer of its elementary Thompson subgroup. -/
theorem lt_normalizer_of_sylow_thompson
    (B E : Subgroup G) (hBE : B ≤ normalizer (E : Set G))
    (S : Sylow 2 B) (hJ : (elementaryAbelianMaxJ (S : Subgroup B)).map B.subtype = E)
    (P : Sylow 2 G) (hSP : (S : Subgroup B).map B.subtype < (P : Subgroup G)) :
    B < normalizer (E : Set G) := by
  let D := (S : Subgroup B).map B.subtype
  have hDB : D ≤ B := map_subtype_le _
  have hDP : D ≤ P := hSP.le
  have hJN : normalizer (D : Set G) ≤ normalizer (E : Set G) := by
    have hh := normalizer_le_normalizer_elementaryAbelianMaxJ D
    rw [elementaryAbelianMaxJ_map_injective B.subtype B.subtype_injective,hJ] at hh
    exact hh
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  have hproper : D.subgroupOf (P : Subgroup G) < ⊤ := by
    rw [lt_top_iff_ne_top,Ne,subgroupOf_eq_top]
    exact not_le_of_gt hSP
  obtain ⟨x,hx,hxD⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (D.subgroupOf (P : Subgroup G)) hproper)
  have hxN : (x : G) ∈ normalizer (D : Set G) := by
    rw [←subgroupOf_normalizer_eq hDP] at hx
    exact hx
  have hPB : (P : Subgroup G).subgroupOf B = (S : Subgroup B) := by
    apply S.is_maximal' P.isPGroup'.comap_subtype
    intro s hs
    exact hDP (mem_map_of_mem B.subtype hs)
  have hxB : (x : G) ∉ B := by
    intro hb
    have hxS : (⟨x,hb⟩ : B) ∈ (S : Subgroup B) :=
      hPB ▸ (show (⟨x,hb⟩ : B) ∈ (P : Subgroup G).subgroupOf B from x.property)
    exact hxD (mem_map_of_mem B.subtype hxS)
  exact lt_of_le_of_ne hBE (fun hh => hxB (hh.symm ▸ hJN hxN))
end Theory.GroupTheory
