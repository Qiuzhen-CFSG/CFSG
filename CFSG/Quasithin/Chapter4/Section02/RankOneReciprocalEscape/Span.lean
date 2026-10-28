module
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Core
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# The actual conjugate span in the reciprocal branch

An index-two intersection is normal in H, so it contains the H-conjugate
span of L. The component core supplies a nontrivial core in that span.
Its characteristic core normalizer is two-local and contains H, hence
maximality gives N_G(〈L^H〉)=H. No ambient normality of L is assumed.

Source: Aschbacher--Smith, 4.2.8, printed p.609.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G]

/-- The ambient normalizer in 4.2.8, using the unchanged component embedding. -/
theorem conjugateSpan_normalizer {L H : Subgroup G}
    (hH : IsMaximalTwoLocal H) (hLH : L ≤ H)
    (hL : (L.subgroupOf H).IsCComponent) (hne : L.pCoreIn 2 ≠ ⊥) :
    normalizer (conjugateSpanBy L H : Set G) = H := by
  let X := conjugateSpanBy L H
  have hLX : L ≤ X := le_conjugateSpanBy L H
  have hXH : X ≤ H := conjugateSpanBy_le_self hLH
  have hHX : H ≤ normalizer (X : Set G) := le_normalizer_conjugateSpanBy L H
  have hc : L.pCoreIn 2 ≤ X.pCoreIn 2 := by
    have hh := map_mono (f := X.subtype)
      (pCoreIn_le_of_subnormal 2 (hL.subgroupOf_of_le hLX hXH).subnormal)
    rwa [map_pCoreIn_of_injective 2 _ X.subtype X.subtype_injective,
      map_subgroupOf_eq_of_le hLX] at hh
  have hXne : X.pCoreIn 2 ≠ ⊥ := fun he => hne (bot_unique (he ▸ hc))
  have hNX : normalizer (X : Set G) ≤ normalizer (X.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image X (pCore 2 X)
  exact le_antisymm
    (hNX.trans (hH.2 ⟨_,hXne,isPGroup_pCoreIn 2 X,rfl⟩ (hHX.trans hNX))) hHX

omit [Finite G] in
/-- In the index-two branch the H-conjugate span stays in the intersection. -/
theorem conjugateSpan_le_intersection {L H M : Subgroup G}
    (hLH : L ≤ H) (hLM : L ≤ M) (hi : (M.subgroupOf H).index = 2) :
    conjugateSpanBy L H ≤ H ⊓ M := by
  let : (M.subgroupOf H).Normal := normal_of_index_eq_two hi
  have hn : H ≤ normalizer ((H ⊓ M : Subgroup G) : Set G) := by
    have hh := (M.subgroupOf H).le_normalizer_map H.subtype
    rw [normalizer_eq_top, ←MonoidHom.range_eq_map,range_subtype,
      subgroupOf_map_subtype] at hh
    simpa only [inf_comm M H] using hh
  exact conjugateSpanBy_le (le_inf hLH hLM) hn
end CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
