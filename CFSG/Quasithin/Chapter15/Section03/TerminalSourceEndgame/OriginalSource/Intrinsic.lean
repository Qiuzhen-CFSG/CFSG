module

public import CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.OriginalSource.Ambient

/-!
# Restricting the original source configuration

Every field of the terminal intersection input is constructed along the actual
inclusion G₀ → G. The local and odd quotient equivalences use subgroup restriction
and the original conjugation. Injectivity transports the two-cores, commutators,
Thompson subgroups and the common Sylow; the stated source 68(2) supplies exactly
the remaining ambient-core centrality bound.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.66–68
and the final proof of 15.3.1, printed pp.1152–1155.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.OriginalSource

open Subgroup Stellmacher AbelianAmalgam
open scoped IsMulCommutative Pointwise

universe u
variable {G : Type u} [Group G] [Finite G]

/-- Restrict a core quotient along the literal subgroup inclusion. -/
noncomputable def restrictedCoreQuotientEquiv {A H : Subgroup G} (hAH : A ≤ H) :
    (A.subgroupOf H ⧸ pCore 2 (A.subgroupOf H)) ≃* (A ⧸ pCore 2 A) :=
  QuotientGroup.congr _ _ (subgroupOfEquivOfLe hAH)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hAH))

omit [Finite G] in
theorem restricted_centralizer {V H : Subgroup G} (hVH : V ≤ H) :
    (centralizer (V : Set G)).subgroupOf H = centralizer ((V).subgroupOf H : Set H) := by
  ext x
  constructor
  · intro hx v hv
    exact Subtype.ext (hx v.val hv)
  · intro hx v hv
    exact congrArg Subtype.val (hx ⟨v, hVH hv⟩ hv)

namespace SourceData

variable {T : Sylow 2 G} {M Mc P E : Subgroup G} {s : G}
  (d : SourceData T M Mc P E s)
include d

local notation "V" => localModule T M
local notation "Y" => residualY M Mc
local notation "F₀" => otherLine E s
local notation "D" => lineT (T : Subgroup G) E
local notation "H" => sourceGroup T M Mc E s
local notation "A₁" => firstAmalgamGroup Y (T : Subgroup G) E F₀
local notation "A₂" => secondAmalgamGroup (T : Subgroup G) E

theorem thompson_map :
    (elementaryAbelianMaxJ (d.sourceSylow : Subgroup H)).map (H).subtype =
      elementaryAbelianMaxJ D := by
  rw [← elementaryAbelianMaxJ_map_injective (H).subtype (H).subtype_injective,
    d.sourceSylow_map]

theorem thompson_eq_restriction :
    elementaryAbelianMaxJ (d.sourceSylow : Subgroup H) =
      (elementaryAbelianMaxJ D).subgroupOf H := by
  apply map_injective (H).subtype_injective
  rw [d.thompson_map, map_subgroupOf_eq_of_le
    ((show elementaryAbelianMaxJ D ≤ D from sSup_le fun _ hA => hA.1).trans
      (common_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s)))]

/-- Every field of the terminal intersection input follows from the source
66/67 outputs and the stated 68(2) centrality input. -/
noncomputable def sourceInput :
    TerminalRecognition.Intersection.SourceInput ((V).subgroupOf H) where
  T := d.sourceSylow
  YF := (lineY Y F₀).subgroupOf H
  XE := (lineX E).subgroupOf H
  G1 := (A₁).subgroupOf H
  G2 := (A₂).subgroupOf H
  R := (centralizer (V : Set G)).subgroupOf H
  F := (F₀).subgroupOf H
  first_local := by
    apply map_injective (H).subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (first_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s)),
      map_subgroupOf_eq_of_le (first_residual_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s)), d.sourceSylow_map]
    rfl
  second_local := by
    apply map_injective (H).subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (second_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s)),
      map_subgroupOf_eq_of_le (second_residual_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s)), d.sourceSylow_map]
    rfl
  generated := by
    apply map_injective (H).subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (first_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s)),
      map_subgroupOf_eq_of_le (second_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s)),
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  common_sylow := by
    rw [d.sourceSylow_eq]
    change ((A₁).comap (H).subtype) ⊓ ((A₂).comap (H).subtype) = (D).comap (H).subtype
    rw [← comap_inf, d.terminal.intersection]
  first_quotient := by
    obtain ⟨e⟩ := d.terminal.quotient_first
    exact ⟨(restrictedCoreQuotientEquiv (first_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s))).trans e⟩
  second_quotient := by
    obtain ⟨e⟩ := d.terminal.quotient_second
    exact ⟨(restrictedCoreQuotientEquiv (second_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s))).trans e⟩
  first_normalized := by
    rw [← subgroupOf_normalizer_eq (first_residual_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s))]
    exact comap_mono d.first_normalized
  second_normalized := by
    rw [← subgroupOf_normalizer_eq (second_residual_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s))]
    exact comap_mono (second_normalized (T := T) (E := E))
  first_perfect :=
    (first_perfect (M := M) (Mc := Mc) (E := E) (s := s)).of_surjective
      (subgroupOfEquivOfLe (first_residual_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s))).symm.toMonoidHom
      (subgroupOfEquivOfLe (first_residual_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s))).symm.surjective
  second_perfect :=
    (second_perfect (E := E)).of_surjective
      (subgroupOfEquivOfLe (second_residual_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s))).symm.toMonoidHom
      (subgroupOfEquivOfLe (second_residual_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s))).symm.surjective
  first_residual := by
    have hlocal : (A₁).subgroupOf H =
        (lineY Y F₀).subgroupOf H ⊔ (d.sourceSylow : Subgroup H) := by
      apply map_injective (H).subtype_injective
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (first_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s)),
        map_subgroupOf_eq_of_le (first_residual_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s)), d.sourceSylow_map]
      rfl
    rw [hlocal]
    apply embedded_pResidual_join_pGroup
    · exact (first_perfect (M := M) (Mc := Mc) (E := E) (s := s)).of_surjective
        (subgroupOfEquivOfLe (first_residual_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s))).symm.toMonoidHom
        (subgroupOfEquivOfLe (first_residual_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s))).symm.surjective
    · exact d.sourceSylow.isPGroup'
    · rw [d.sourceSylow_eq, ← subgroupOf_normalizer_eq (first_residual_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s))]
      exact comap_mono (le_sup_right.trans d.first_normalized)
  second_residual := by
    have hlocal : (A₂).subgroupOf H =
        (lineX E).subgroupOf H ⊔ (d.sourceSylow : Subgroup H) := by
      apply map_injective (H).subtype_injective
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (second_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s)),
        map_subgroupOf_eq_of_le (second_residual_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s)), d.sourceSylow_map]
      rfl
    rw [hlocal]
    apply embedded_pResidual_join_pGroup
    · exact (second_perfect (E := E)).of_surjective
        (subgroupOfEquivOfLe (second_residual_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s))).symm.toMonoidHom
        (subgroupOfEquivOfLe (second_residual_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s))).symm.surjective
    · exact d.sourceSylow.isPGroup'
    · rw [d.sourceSylow_eq, ← subgroupOf_normalizer_eq (second_residual_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s))]
      exact comap_mono (le_sup_right.trans (second_normalized (T := T) (E := E)))
  first_odd_quotient := by
    obtain ⟨e⟩ := d.first_odd_quotient
    exact ⟨(restrictedCoreQuotientEquiv (first_residual_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s))).trans e⟩
  second_odd_quotient := by
    obtain ⟨e⟩ := d.second_odd_quotient
    exact ⟨(restrictedCoreQuotientEquiv (second_residual_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s))).trans e⟩
  centralizer_eq := restricted_centralizer d.vector_le_group
  sylow_centralizer_eq := by
    rw [← restricted_centralizer d.vector_le_group, d.sourceSylow_eq]
    exact (inf_eq_right.mpr (comap_mono d.centralizer_le_common)).symm
  vector_le_core := by
    intro v hv
    obtain ⟨q, hq, he⟩ := d.terminal.module_le_core hv
    exact (Subtype.ext he : q = v) ▸ hq
  core_bound := by
    apply (map_le_iff_le_comap).mp
    rw [Subgroup.map_sup, map_pCoreIn_of_injective 2 _ _ (H).subtype_injective,
      map_subgroupOf_eq_of_le (first_residual_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s))]
    exact sup_le d.centrality d.first_residual_core_centralizes
  three_prime_core := d.terminal.core_eq
  second_escape := by
    intro hx
    have h : ((lineX E).subgroupOf H).map (H).subtype ≤
        (d.sourceSylow : Subgroup H).map (H).subtype :=
      map_mono (hx.trans (pCore_isPGroup.le_sylow_of_normal d.sourceSylow))
    rw [map_subgroupOf_eq_of_le (second_residual_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s)), d.sourceSylow_map] at h
    exact d.residual_escape (h.trans (inf_le_left.trans d.sylow_le))
  second_commutator := by
    apply map_injective (H).subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le (second_residual_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s)),
      d.thompson_map]
    exact d.second_thompson_commutator
  sylow_thompson := by
    apply map_injective (H).subtype_injective
    rw [d.thompson_map, ← elementaryAbelianMaxJ_map_injective
      (H).subtype (H).subtype_injective,
      map_subgroupOf_eq_of_le (d.centralizer_le_common.trans (common_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s)))]
    exact d.thompson_centralizer
  thompson_normalized := by
    rw [d.thompson_eq_restriction, ← subgroupOf_normalizer_eq
      ((show elementaryAbelianMaxJ D ≤ D from sSup_le fun _ hA => hA.1).trans
        (common_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s)))]
    exact comap_mono d.thompson_normalized
  vector_commutator := by
    apply map_injective (H).subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le d.vector_le_group,
      map_subgroupOf_eq_of_le (first_residual_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s))]
    exact d.first_vector_commutator
  vector_card := (Nat.card_congr (subgroupOfEquivOfLe d.vector_le_group).toEquiv).trans
    d.vector_card
  local_commutator := by
    apply map_injective (H).subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le d.vector_le_group,
      map_pCoreIn_of_injective 2 _ _ (H).subtype_injective,
      map_subgroupOf_eq_of_le (first_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s)),
      map_subgroupOf_eq_of_le d.singular_le_group]
    exact d.local_vector_commutator
  singular_nontrivial := by
    intro h
    have hc : Nat.card ((F₀).subgroupOf H) = 4 :=
      (Nat.card_congr (subgroupOfEquivOfLe d.singular_le_group).toEquiv).trans
        d.terminal.line_card
    rw [h, Subgroup.card_bot] at hc
    omega

end SourceData
end CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.OriginalSource
