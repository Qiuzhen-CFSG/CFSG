module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Selection
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents

/-!
# Initial comparison of the point and line components

The literal line component lies in the point component. We remove the
line-normalizer supplement using 11.2.3 and characteristic invariance of
N_L(V1)^infinity. If the point component normalizes the line, restriction
and comparison of C-components force equality. Thus a strict comparison
moves the line. The point component belongs to the actual local family,
and every proper local overcomponent moves the original point.

EarlierGeometry retains only the specified point and the earlier
11.1.1/11.2.3 conclusions. Its existence is not asserted here. Neither
component equality nor any classification or exclusion branch is a field.
All component statements are relative to Gz or G1.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.4.2, printed pp.776--777, initial and maximal-overcomponent reductions.
-/

open Subgroup
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- Earlier source inputs for the literal comparison. The normalizer
supplement is used only after fixed-space vanishing has been proved. -/
structure EarlierGeometry : Prop where
  point_mem : E.z ∈ E.V₁
  point_fixed : E.z ∈ centralizer (T : Set G)
  point_ne_one : E.z ≠ 1
  seed_centralizes : E.L₁ ≤ centralizer (E.V₁ : Set G)
  line_component : Source.ComponentIn E.G₁ E.K
  point_component : Source.ComponentIn (Gz E) E.Kz
  normalizer_split : V ⊓ centralizer (L : Set G) = ⊥ →
    E.G₁ = centralizer (E.V₁ : Set G) ⊔ E.M₁

namespace EarlierGeometry
variable {E} (h : EarlierGeometry E)
include h

/-- The original Sylow subgroup lies in the actual point centralizer. -/
theorem sylow_le_pointCentralizer : (T : Subgroup G) ≤ Gz E := by
  intro t ht
  exact mem_centralizer_singleton_iff.mpr (h.point_fixed t ht)

omit h in
/-- The common normalizer preserves the literal solvable residual L1. -/
theorem line_stabilizer_normalizes_seed : E.M₁ ≤ normalizer (E.L₁ : Set G) := by
  apply le_trans _ (normalizer_le_normalizer_characteristic_image
    (L ⊓ E.G₁) (solvableResidual (L ⊓ E.G₁ : Subgroup G)))
  exact (le_inf (show E.M₁ ≤ normalizer (L : Set G) from inf_le_left)
    (show E.M₁ ≤ normalizer (E.G₁ : Set G) from inf_le_right.trans E.G₁.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf

/-- The line component centralizes the entire source line. -/
theorem line_component_centralizes : E.K ≤ centralizer (E.V₁ : Set G) :=
  conjugateSpanBy_le h.seed_centralizes (normalizer_le_normalizer_centralizer E.V₁)

/-- Remove the seed-preserving supplement to compare the two closures. -/
theorem line_component_le_point (hf : V ⊓ centralizer (L : Set G) = ⊥) : E.K ≤ E.Kz := by
  change conjugateSpanBy E.L₁ E.G₁ ≤ conjugateSpanBy E.L₁ (Gz E)
  rw [h.normalizer_split hf, conjugateSpanBy_sup_of_normalizes_seed _ _ _
    (line_stabilizer_normalizes_seed (E := E))
    ((show E.M₁ ≤ E.G₁ from inf_le_right).trans
      (normalizer_le_normalizer_centralizer E.V₁))]
  exact conjugateSpanBy_mono le_rfl (centralizer_le (Set.singleton_subset_iff.mpr h.point_mem))

/-- Restrict both C-components to Kz; comparability forces equality. -/
theorem eq_of_point_normalizes_line (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hn : E.Kz ≤ E.G₁) : E.Kz = E.K := by
  have hle := h.line_component_le_point hf
  have ha := h.line_component.2.subgroupOf_of_le hle hn
  have hb := h.point_component.2.subgroupOf_of_le le_rfl h.point_component.1
  have he := ha.eq_of_le hb (comap_mono hle)
  have hm := congrArg (map E.Kz.subtype) he
  simpa only [map_subgroupOf_eq_of_le hle, map_subgroupOf_eq_of_le le_rfl] using hm.symm

/-- The remaining equality is precisely the line-centralization problem. -/
theorem eq_iff_point_centralizes_line (hf : V ⊓ centralizer (L : Set G) = ⊥) :
    E.Kz = E.K ↔ E.Kz ≤ centralizer (E.V₁ : Set G) := by
  constructor
  · intro he
    exact he ▸ h.line_component_centralizes
  · intro hc
    exact h.eq_of_point_normalizes_line hf (hc.trans (Subgroup.centralizer_le_normalizer _))

/-- A counterexample gives both strict inclusions and movement of the line. -/
theorem strict_comparison (hf : V ⊓ centralizer (L : Set G) = ⊥) (hne : E.Kz ≠ E.K) :
    E.K < E.Kz ∧ E.L₁ < E.Kz ∧ ¬ E.Kz ≤ E.G₁ := by
  have hlt : E.K < E.Kz := lt_of_le_of_ne (h.line_component_le_point hf) hne.symm
  exact ⟨hlt, lt_of_le_of_lt (le_conjugateSpanBy _ _) hlt,
    fun hn => hne (h.eq_of_point_normalizes_line hf hn)⟩

/-- The point two-local and its C-component give genuine local-family membership. -/
theorem point_mem_local_family : E.Kz ∈ Chapter1.L G (T : Subgroup G) := by
  have hlocal := point_twoLocal E h.point_mem h.point_fixed h.point_ne_one
  exact Chapter1.mem_L_of_cComponent (Chapter1.mem_H_of_isTwoLocal hlocal)
    ⟨T.subtype h.sylow_le_pointCentralizer, by
      simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le h.sylow_le_pointCentralizer]⟩
    h.point_component.1 h.point_component.2

/-- Finite maximal descent constructs the source K-plus in L-star(G,T). -/
theorem exists_maximal_overcomponent :
    ∃ Kplus ∈ Chapter1.LStar G (T : Subgroup G), E.Kz ≤ Kplus :=
  Chapter1.exists_mem_LStar_ge h.point_mem_local_family

/-- A local overcomponent inside Gz is the same C-component. -/
theorem overcomponent_eq_of_centralizes_point {Kplus : Subgroup G}
    (hloc : Kplus ∈ Chapter1.L G (T : Subgroup G)) (hle : E.Kz ≤ Kplus)
    (hc : Kplus ≤ Gz E) : Kplus = E.Kz := by
  have hj : Kplus ⊔ (T : Subgroup G) ≤ Gz E := sup_le hc h.sylow_le_pointCentralizer
  have hk := h.point_component.2.subgroupOf_of_le (hle.trans le_sup_left) hj
  have he := hk.eq_of_le hloc.1 (comap_mono hle)
  have hm := congrArg (map (Kplus ⊔ (T : Subgroup G)).subtype) he
  simpa only [map_subgroupOf_eq_of_le (show Kplus ≤ Kplus ⊔ (T : Subgroup G) from le_sup_left),
    map_subgroupOf_eq_of_le (hle.trans le_sup_left)] using hm.symm

/-- Every proper local overcomponent moves z, as required on p.776. -/
theorem proper_overcomponent_moves_point {Kplus : Subgroup G}
    (hloc : Kplus ∈ Chapter1.L G (T : Subgroup G)) (hlt : E.Kz < Kplus) :
    ¬ Kplus ≤ Gz E := by
  intro hc
  exact hlt.ne' (h.overcomponent_eq_of_centralizes_point hloc hlt.le hc)

end EarlierGeometry

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
