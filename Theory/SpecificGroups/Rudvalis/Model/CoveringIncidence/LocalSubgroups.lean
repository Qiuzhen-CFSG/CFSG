module

public import Theory.SpecificGroups.Rudvalis.Model.CoreQuotients

/-!
# Intrinsic core and center of the fixed Rudvalis max4 subgroup

Use the actual intrinsic O₂(max4), embedded back into Ru, and then its
actual center. The marked elementary eight-group is normal in max4 and
therefore lies in the core. Full image of its conjugation action identifies
the core with its relative centralizer and puts the eight-group in the
core center. Equality with that center and the Steinberg quotient are
separate concrete calculations, not definitions.

Source: Aschbacher--Smith I.2.2(7), printed p.412; GLS3 Table 5.3r and its
justification on pp.291--292. All ATLAS words are inherited unchanged.
-/

namespace Rudvalis.CoveringIncidence

open Subgroup SylowOvergroups CoreQuotients
open SylowOvergroups.RadicalCoverage.LocalCover

/-- P* is the intrinsic two-core of the fixed max4, viewed in Ru. -/
@[expose] public def max4Core : Subgroup Model :=
  (pCore 2 max4).map max4.subtype

/-- V* is the actual center of P*, viewed in Ru. -/
@[expose] public def max4CoreCenter : Subgroup Model :=
  (center max4Core).map max4Core.subtype

public theorem max4Core_le_max4 : max4Core ≤ max4 := map_subtype_le _

public theorem max4CoreCenter_le_core : max4CoreCenter ≤ max4Core := map_subtype_le _

/-- The marked eight-group belongs to the fixed max4, via the checked local words. -/
public theorem marked_eight_le_max4 : elementary 2 ≤ max4 :=
  (elementary_le_localP 2).trans localP_le_max4

/-- Its normality is relative to max4, as required for the intrinsic core. -/
public theorem marked_eight_normal_in_max4 : ((elementary 2).subgroupOf max4).Normal :=
  (normal_subgroupOf_iff_le_normalizer marked_eight_le_max4).mpr
    RankOneEightAction.max4_le_normalizer_eight

/-- The normal elementary eight-group lies in the intrinsic max4 two-core. -/
public theorem marked_eight_le_core : elementary 2 ≤ max4Core := by
  have hp : IsPGroup 2 (elementary 2) :=
    IsPGroup.of_card (n := 3) RankOneEightCharacteristic.elementary_two_card
  have hle : (elementary 2).subgroupOf max4 ≤ pCore 2 max4 :=
    le_sSup ⟨marked_eight_normal_in_max4, hp.comap_subtype⟩
  have hm := map_mono (f := max4.subtype) hle
  rwa [map_subgroupOf_eq_of_le marked_eight_le_max4] at hm

/-- Under the independent full-image calculation, the actual core centralizes
the marked eight-group. -/
public theorem core_le_centralizer_eight_of_full_image
    (h : Function.Surjective max4EightAction) :
    max4Core ≤ centralizer (elementary 2 : Set Model) := by
  rintro x ⟨g, hg, rfl⟩
  rw [← max4_centralizer_eq_pCore_of_full_image h] at hg
  exact hg

/-- Consumer application: the full-image calculation places the marked E₈
inside the literal V*=Z(P*), with the same ambient embedding. -/
public theorem marked_eight_le_core_center_of_full_image
    (h : Function.Surjective max4EightAction) : elementary 2 ≤ max4CoreCenter := by
  intro x hx
  refine ⟨⟨x, marked_eight_le_core hx⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  have hy := core_le_centralizer_eight_of_full_image h y.property
  exact (mem_centralizer_iff.mp hy x hx).symm

end Rudvalis.CoveringIncidence
