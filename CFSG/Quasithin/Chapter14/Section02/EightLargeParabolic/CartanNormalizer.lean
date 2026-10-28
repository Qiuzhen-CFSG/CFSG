module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.Completion
public import Theory.SpecificGroups.Triality.BinaryTorusNormalizer

/-!
# The seven-torus normalizer on the original triality marking

The literal middle map, followed by the generated subgroup's inclusion in G,
sends the native unipotent group to the original Sylow T. Consequently the
native eight-element torus centralizer is exactly C_T(Q). The normalizer of Q
inside the whole original overlap is its centralizer, of order 56. These facts
retain the same Q used by the aligned actual endpoint reflections.

The middle commuting square is used explicitly; no ambient recognition or
replacement amalgam is assumed. The native hexagon relation remains a separate
obligation. Source: Aschbacher--Smith F.4.15--17 and14.2.18--19, pp.281--283,987.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.ConcreteBruhat
local notation "P" => binaryParameters 1 Nat.zero_lt_one
variable {G : Type*} [Group G] {T : Sylow 2 G} {M Mc H : Subgroup G}

/-- The unchanged marked middle, followed by its literal ambient inclusion. -/
abbrev ambientBorelMap (r : MarkedTriality T M Mc H) : borel P →* G :=
  (H ⊔ secondParabolic T M Mc H).subtype.comp (markedCompletion r).middle

/-- The torus already used for the aligned reflection pair, inside the original G. -/
abbrev ambientTorus (r : MarkedTriality T M Mc H) : Subgroup G :=
  ((torus P).subgroupOf (borel P)).map (ambientBorelMap r)

theorem ambientBorelMap_injective (r : MarkedTriality T M Mc H) :
    Function.Injective (ambientBorelMap r) :=
  Subtype.val_injective.comp (markedCompletion r).middle_injective

/-- The middle commuting square retains the original overlap elements. -/
theorem ambientBorelMap_eq (r : MarkedTriality T M Mc H) :
    ambientBorelMap r = (H ⊓ secondParabolic T M Mc H).subtype.comp
      r.middle.symm.toMonoidHom := by
  ext b
  exact congrArg H.subtype (r.symm.left_commutes b)

theorem ambientBorelMap_range (r : MarkedTriality T M Mc H) :
    (ambientBorelMap r).range = H ⊓ secondParabolic T M Mc H := by
  rw [ambientBorelMap,← MonoidHom.map_range]
  exact markedCompletion_middle_image r


/-- The unipotent subgroup under this same ambient map is the original Sylow. -/
theorem ambientBorelMap_unipotent [Finite G] (r : MarkedTriality T M Mc H)
    (hTH : (T : Subgroup G) ≤ H) :
    ((unipotent P).subgroupOf (borel P)).map (ambientBorelMap r) = T := by
  let B := H ⊓ secondParabolic T M Mc H
  have hTB : (T : Subgroup G) ≤ B := le_inf hTH (le_sup_right.trans le_sup_left)
  have he : ((T : Subgroup G).subgroupOf B).map r.middle.toMonoidHom =
      (unipotent P).subgroupOf (borel P) := by
    apply map_injective (borel P).subtype_injective
    rw [map_subgroupOf_eq_of_le (unipotent_le_borel P)]
    exact middle_sylow_map r hTH
  have hd : ((unipotent P).subgroupOf (borel P)).map r.middle.symm.toMonoidHom =
      (T : Subgroup G).subgroupOf B := by
    apply map_injective (f := r.middle.toMonoidHom) r.middle.injective
    rw [map_map]
    have hh : r.middle.toMonoidHom.comp r.middle.symm.toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      exact r.middle.apply_symm_apply x
    rw [hh,map_id]
    exact he.symm
  rw [ambientBorelMap_eq,← map_map,hd,map_subgroupOf_eq_of_le hTB]

/-- The marked seven-torus has its original ambient order. -/
theorem ambientTorus_card (r : MarkedTriality T M Mc H) : Nat.card (ambientTorus r) = 7 := by
  rw [ambientTorus,card_map_of_injective (ambientBorelMap_injective r),
    Nat.card_congr (subgroupOfEquivOfLe (torus_le_borel P)).toEquiv,
    TorusCoordinates.card_torus P rfl]
  rfl

/-- Inside the actual overlap, normalization of the fixed torus is centralization. -/
theorem ambientTorus_overlap_normalizer (r : MarkedTriality T M Mc H) :
    (H ⊓ secondParabolic T M Mc H) ⊓ normalizer (ambientTorus r : Set G) =
      (H ⊓ secondParabolic T M Mc H) ⊓ centralizer (ambientTorus r : Set G) := by
  rw [←ambientBorelMap_range r]
  exact BinaryTorusCentralizer.borel_embedding_normalizer_eq_centralizer
    (ambientBorelMap r) (ambientBorelMap_injective r)

/-- The overlap's actual torus normalizer has order 56. -/
theorem ambientTorus_overlap_normalizer_card (r : MarkedTriality T M Mc H) :
    Nat.card ((H ⊓ secondParabolic T M Mc H) ⊓ normalizer
      (ambientTorus r : Set G) : Subgroup G) = 56 := by
  rw [←ambientBorelMap_range r]
  exact BinaryTorusCentralizer.borel_embedding_normalizer_card
    (ambientBorelMap r) (ambientBorelMap_injective r)

/-- The centralizer of the marked torus in the original Sylow has order eight. -/
theorem ambientTorus_sylow_centralizer_card [Finite G] (r : MarkedTriality T M Mc H)
    (hTH : (T : Subgroup G) ≤ H) :
    Nat.card ((T : Subgroup G) ⊓ centralizer (ambientTorus r : Set G) : Subgroup G) = 8 := by
  rw [←ambientBorelMap_unipotent r hTH]
  exact BinaryTorusCentralizer.borel_embedding_unipotent_centralizer_card
    (ambientBorelMap r) (ambientBorelMap_injective r)
/-- The torus normalizer within the original Sylow is exactly its centralizer. -/
theorem ambientTorus_sylow_normalizer (r : MarkedTriality T M Mc H)
    (hTH : (T : Subgroup G) ≤ H) :
    (T : Subgroup G) ⊓ normalizer (ambientTorus r : Set G) =
      (T : Subgroup G) ⊓ centralizer (ambientTorus r : Set G) := by
  apply le_antisymm _ (inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _))
  rintro x ⟨hx,hn⟩
  have hB : x ∈ H ⊓ secondParabolic T M Mc H :=
    ⟨hTH hx,(show (T : Subgroup G) ≤ secondParabolic T M Mc H from
      le_sup_right.trans le_sup_left) hx⟩
  exact ⟨hx,((ambientTorus_overlap_normalizer r).le ⟨hB,hn⟩).2⟩

/-- This actual Sylow normalizer also has order eight. -/
theorem ambientTorus_sylow_normalizer_card [Finite G] (r : MarkedTriality T M Mc H)
    (hTH : (T : Subgroup G) ≤ H) :
    Nat.card ((T : Subgroup G) ⊓ normalizer (ambientTorus r : Set G) : Subgroup G) = 8 := by
  rw [ambientTorus_sylow_normalizer r hTH]
  exact ambientTorus_sylow_centralizer_card r hTH

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
