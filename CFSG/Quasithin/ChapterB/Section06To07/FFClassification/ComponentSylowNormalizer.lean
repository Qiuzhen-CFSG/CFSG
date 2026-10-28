module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.ComponentAutomizer

/-!
# Component Sylow normalizers lie in the original maximal overgroup

The Sylow intersection with an even simple component is nontrivial. Its
normalizer in that component is proper, since normality of the intersection
would make the perfect component a two-group. The actual Sylow stabilizer
normalizes this seed, so the source component-seed theorem places it in the
unique maximal overgroup. The paired S₅ application uses its A₄ Borel.

Source: Aschbacher--Smith B.6.8(3), C.1.24 and E.2.3(3).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]

theorem component_sylow_normalizer_le_maximal
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    {L : Subgroup G} (hL : IsComponent G L) [IsSimpleGroup L]
    (heven : 2 ∣ Nat.card L) :
    L ⊓ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) ≤
      minimalParabolicMax T hP := by
  let P : Subgroup G := (T : Subgroup G) ⊓ L
  let A := L ⊓ normalizer (P : Set G)
  have hPne : P ≠ ⊥ := by
    intro hb
    apply component_sylow_intersection_ne_bot T hL heven
    apply le_bot_iff.mp
    intro x hx
    have hh : (x : G) ∈ P := ⟨hx,x.property⟩
    rw [hb,mem_bot] at hh
    exact Subtype.ext hh
  have hPA : P ≤ A := le_inf inf_le_right P.le_normalizer
  have hAne : A ≠ ⊥ := fun h => hPne (le_bot_iff.mp (h ▸ hPA))
  have hAL : A ≠ L := by
    intro h
    have hLn : L ≤ normalizer (P : Set G) := h ▸ inf_le_right
    let : (P.subgroupOf L).Normal := (normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hLn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.subgroupOf L) inferInstance with hb | ht
    · apply hPne
      have hh := congrArg (map L.subtype) hb
      simpa only [map_subgroupOf_eq_of_le (show P ≤ L from inf_le_right),Subgroup.map_bot] using hh
    · have hLP : L ≤ P := by
        intro x hx
        have hxp : (⟨x,hx⟩ : L) ∈ P.subgroupOf L := ht ▸ mem_top _
        exact hxp
      have hp : IsPGroup 2 L := T.isPGroup'.to_le (hLP.trans inf_le_left)
      let := hp.isNilpotent
      let := hL.2
      exact Group.IsPerfect.not_isSolvable L inferInstance
  have hinv : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (A : Set G) := by
    have hnP : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (P : Set G) :=
      (le_inf (inf_le_left.trans (T : Subgroup G).le_normalizer) inf_le_right).trans
        inf_normalizer_le_normalizer_inf
    exact (le_inf inf_le_right (hnP.trans (normalizer (P : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact component_seed_le_minimalParabolicMax T hP hL inf_le_left hAne hAL hinv
end CFSG.Quasithin.ChapterB
