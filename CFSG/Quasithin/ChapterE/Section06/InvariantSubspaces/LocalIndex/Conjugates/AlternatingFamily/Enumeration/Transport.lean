module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration.Setup

/-!
# Returning the intrinsic four-family calculation to the ambient group

The maximum elementary family inside the group `S` maps bijectively to the
maximum elementary family of the subgroup `S ≤ G`: both the elementary
condition and every order comparison are transported. The same subtype map
respects the given permutation action. This adapter retains the full maximum
family, not only a collection of elementary candidates.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the proof of
C.5.6, printed pp.157–158.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration
open Subgroup
universe u
variable {G : Type u} [Group G]

private theorem maxFamily_map_subtype_iff (T : Subgroup G) (B : Subgroup T) :
    B.map T.subtype ∈ Stellmacher.elementaryAbelianMaxSubgroups T ↔
      B ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T) := by
  constructor
  · intro hB
    let : IsElementaryAbelian 2 (B.map T.subtype) := hB.2.1
    have he : (B.map T.subtype).subgroupOf T = B :=
      comap_map_eq_self_of_injective T.subtype_injective B
    have hBe : IsElementaryAbelian 2 B :=
      he ▸ IsElementaryAbelian.subgroupOf (map_subtype_le B)
    refine ⟨le_top, hBe, ?_⟩
    intro Y _ hYe
    have hc := hB.2.2 (Y.map T.subtype) (map_subtype_le Y) (hYe.map T.subtype)
    simpa only [card_map_of_injective T.subtype_injective] using hc
  · intro hB
    refine ⟨map_subtype_le B, hB.2.1.map T.subtype, ?_⟩
    intro Y hY hYe
    let : IsElementaryAbelian 2 Y := hYe
    have hc := hB.2.2 (Y.subgroupOf T) le_top (IsElementaryAbelian.subgroupOf hY)
    rw [card_map_of_injective T.subtype_injective]
    exact (Nat.card_congr (subgroupOfEquivOfLe hY).toEquiv).symm.le.trans hc

private theorem maxFamily_eq_image (T : Subgroup G) :
    Stellmacher.elementaryAbelianMaxSubgroups T =
      (fun B : Subgroup T => B.map T.subtype) ''
        Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T) := by
  ext E
  constructor
  · intro hE
    refine ⟨E.subgroupOf T, ?_, map_subgroupOf_eq_of_le hE.1⟩
    apply (maxFamily_map_subtype_iff T _).mp
    rwa [map_subgroupOf_eq_of_le hE.1]
  · rintro ⟨B, hB, rfl⟩
    exact (maxFamily_map_subtype_iff T B).mpr hB

variable {R L : Subgroup G}

/-- The intrinsic and ambient action-image conventions agree on mapped subgroups. -/
theorem actionImage_map_subtype (c : ActionCoordinates R L) (B : Subgroup (S R)) :
    actionImage c.action (B.map (S R).subtype) = B.map (restrictedAction c) := by
  rw [← restrictedAction_image c (map_subtype_le B)]
  have he : (B.map (S R).subtype).subgroupOf (S R) = B :=
    comap_map_eq_self_of_injective (S R).subtype_injective B
  rw [he]

/-- A proved intrinsic enumeration gives exactly the original ambient contract.
The substantive maximum-order and exhaustion hypothesis is deliberately explicit. -/
theorem family_of_intrinsic_enumeration {H : Subgroup G} {x : G}
    (hb : BaumannStructure H R L) (hp : Factorization R L x)
    (c : ActionCoordinates R L) {B₀ B₁ : Subgroup (S R)}
    (hfamily : Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup (S R)) =
      {coreIn R L, oppositeIn R L x, B₀, B₁})
    (h0 : B₀.map (restrictedAction c) = line 0)
    (h1 : B₁.map (restrictedAction c) = line 1) :
    ∃ E₀ E₁ : Subgroup G,
      Stellmacher.elementaryAbelianMaxSubgroups (S R) =
        {Q R L, opposite R L x, E₀, E₁} ∧
      actionImage c.action E₀ = line 0 ∧ actionImage c.action E₁ = line 1 := by
  refine ⟨B₀.map (S R).subtype, B₁.map (S R).subtype, ?_, ?_, ?_⟩
  · rw [maxFamily_eq_image, hfamily]
    simp only [Set.image_insert_eq, Set.image_singleton, coreIn, oppositeIn,
      map_subgroupOf_eq_of_le (hb.core_eq ▸ inf_le_left),
      map_subgroupOf_eq_of_le (opposite_le_S hp)]
  · rw [actionImage_map_subtype, h0]
  · rw [actionImage_map_subtype, h1]

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration
end
