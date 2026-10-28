module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Configuration
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Restricting the rank-one configuration to its component

The relation `V₂ = [V₂,Y₊]`, with `Y₊ ≤ L` and `I` normalizing `L`,
puts the four-group inside the component. Normal intersection restricts
`S` to a Sylow subgroup of `L`. Transport through an actual model
isomorphism then gives a normal elementary four-subgroup of a model Sylow.

These deductions use the explicit reduction output for Aschbacher--Smith
15.3.43(a)--(e), printed pp.1139--1140 (1 March 2004 manuscript).
Constructing that output remains the responsibility of the source assembly.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.OddModels
variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}

omit [Finite G] in
/-- The moving four-group lies normally in the actual three-prime residual.
This supplies the intrinsic residual input to the alternating-seven calculation. -/
theorem plane_normal_in_residual (c : ReducedConfiguration Yplus S M I L V₁ V₂) :
    V₂ ≤ Yplus ∧ (V₂.subgroupOf Yplus).Normal := by
  have hSI : S ≤ I := le_sup_right.trans c.minimal.1.1.2
  have hVN : V₂ ≤ normalizer (Yplus : Set G) := by
    intro x hx
    exact (c.normalizer_eq.ge
      ⟨c.sylow_le_M (c.plane_two_le hx), hSI (c.plane_two_le hx)⟩).2
  have hVY : V₂ ≤ Yplus := by
    rw [← c.plane_two_commutator]
    exact le_normalizer_iff_commutator_le_right.mp hVN
  have hYMI : Yplus ≤ M ⊓ I := by
    rw [c.residual]
    exact map_subtype_le _
  exact ⟨hVY, normal_subgroupOf_of_le_normalizer
    (hYMI.trans c.plane_two_normalized)⟩

omit [Finite G] in
theorem plane_le_component (c : ReducedConfiguration Yplus S M I L V₁ V₂) : V₂ ≤ L := by
  have hSI : S ≤ I := le_sup_right.trans c.minimal.1.1.2
  rw [← c.plane_two_commutator]
  exact (commutator_mono le_rfl c.y_le_component).trans
    (le_normalizer_iff_commutator_le_right.mp
      (c.plane_two_le.trans (hSI.trans c.normalizes)))

theorem component_sylow (c : ReducedConfiguration Yplus S M I L V₁ V₂) :
    ∃ T : Sylow 2 L, (T : Subgroup L).map L.subtype = S ⊓ L := by
  obtain ⟨P, hP⟩ := c.sylow
  let : (L.subgroupOf I).Normal := normal_subgroupOf_of_le_normalizer c.normalizes
  obtain ⟨T, hT⟩ := P.exists_subgroupOf_eq_of_normal (L.subgroupOf I)
  let e := subgroupOfEquivOfLe c.component_le
  refine ⟨T.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((T : Subgroup (L.subgroupOf I)).map e.toMonoidHom).map L.subtype = _
  rw [map_map]
  change (T : Subgroup (L.subgroupOf I)).map
    (I.subtype.comp (L.subgroupOf I).subtype) = _
  rw [← map_map, hT, subgroupOf_map_subtype, map_inf _ _ _ I.subtype_injective,
    hP, map_subgroupOf_eq_of_le c.component_le]

theorem normal_four_in_model_sylow (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    {H : Type*} [Group H] (e : L ≃* H) :
    ∃ T : Sylow 2 H, ∃ R : Subgroup T, R.Normal ∧
      IsElementaryAbelian 2 R ∧ Nat.card R = 4 := by
  obtain ⟨P, hP⟩ := component_sylow c
  let T := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let W := (V₂.subgroupOf L).map e.toMonoidHom
  have hVP : V₂.subgroupOf L ≤ P := by
    intro v hv
    have hv' : (v : G) ∈ (P : Subgroup L).map L.subtype := by
      rw [hP]
      exact ⟨c.plane_two_le hv, v.property⟩
    simpa using hv'
  have hWT : W ≤ T := map_mono hVP
  have hPN : (P : Subgroup L) ≤ normalizer (V₂.subgroupOf L : Set L) := by
    rw [← subgroupOf_normalizer_eq (plane_le_component c)]
    intro x hx
    have hxS : (x : G) ∈ S := (hP ▸ mem_map_of_mem L.subtype hx).1
    exact c.plane_two_normalized ⟨c.sylow_le_M hxS, c.component_le x.property⟩
  have hn : (T : Subgroup H) ≤ normalizer (W : Set H) :=
    (map_mono hPN).trans ((V₂.subgroupOf L).le_normalizer_map e.toMonoidHom)
  let : IsElementaryAbelian 2 V₂ := c.plane_two_elementary
  let : IsElementaryAbelian 2 (V₂.subgroupOf L) :=
    IsElementaryAbelian.subgroupOf (plane_le_component c)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map e.toMonoidHom
  refine ⟨T, W.subgroupOf T, normal_subgroupOf_of_le_normalizer hn,
    IsElementaryAbelian.subgroupOf hWT, ?_⟩
  rw [Nat.card_congr (subgroupOfEquivOfLe hWT).toEquiv,
    ← Nat.card_congr (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (plane_le_component c)).toEquiv,
    c.plane_two_card]

end CFSG.Quasithin.Chapter15.Section03.RankOne.OddModels
