module

public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.Movement

/-!
# Radical saturation in the original local group

For the normal C-component in C.2.7, radical saturation inside H places
O₂(KR) inside R. Mapping through H's inclusion retains the literal ambient
subgroups used by the star-quotient normalizer calculation.

Source: Aschbacher--Smith C.2.7, displayed (*), printed p.146.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H K R M : Subgroup G}

theorem source_joinCore_le_radical (h : Input κ H R M K)
    [(K.subgroupOf H).Normal] : (K ⊔ R).pCoreIn 2 ≤ R := by
  have hKm := map_subgroupOf_eq_of_le h.component.1
  have hRm := map_subgroupOf_eq_of_le h.setup.radical_le
  have hJm : (K.subgroupOf H ⊔ R.subgroupOf H).map H.subtype = K ⊔ R := by
    rw [Subgroup.map_sup,hKm,hRm]
  have hm := map_mono (f := H.subtype)
    (joinCore_le_radical (K.subgroupOf H) (R.subgroupOf H) h.setup.radical)
  rwa [map_pCoreIn_of_injective 2 _ _ H.subtype_injective,hJm,hRm] at hm
end CFSG.Quasithin.ChapterC.C27Source
