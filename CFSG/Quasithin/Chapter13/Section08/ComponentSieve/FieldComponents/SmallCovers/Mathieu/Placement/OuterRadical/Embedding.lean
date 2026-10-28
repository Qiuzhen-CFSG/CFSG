module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement.Coordinates
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Ambient
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The faithful design action of the actual star quotient

The relatively normal component maps onto a normal M₂₂ in H/O₂(H).
Since H = KT and T is a two-group, the quotient above that component is
also a two-group. Its centralizer is consequently a normal two-group and
is trivial, as O₂(H/O₂(H)) = 1. Conjugation therefore gives a faithful
map into the concrete design automorphisms, agreeing with the supplied
component coordinates. Its image contains the even subgroup of index two.

Source: Aschbacher–Smith, 13.8.21(2), printed p.956 (PDF p.973).
-/

@[expose] public section
open Subgroup Sporadic.Mathieu Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement
namespace Setup
variable {G : Type*} [Group G] [Finite G]
variable {H K L₁ T G₁ M : Subgroup G} (s : Setup H K L₁ T G₁ M)
include s

omit [Finite G] in
/-- Normality is inside the actual quotient H/O₂(H). -/
theorem star_component_normal : (Source.starImage H K).Normal := by
  let := s.component_normal
  exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

omit [Finite G] in
/-- The source product survives both intersection with H and the star quotient. -/
theorem star_component_join_sylow : Source.starImage H K ⊔ Source.starImage H T = ⊤ := by
  rw [Source.starImage, Source.starImage, ← Subgroup.map_sup,
    ← subgroupOf_sup s.component_le (le_sup_right.trans s.seed_join_sylow_le),
    ← s.eq_component_join_sylow, subgroupOf_self,
    map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

/-- Faithfulness follows from the source setup, with no centralizer assumption. -/
theorem star_component_centralizer :
    centralizer (Source.starImage H K : Set (Source.Hstar H)) = ⊥ := by
  let e := starCoordinates H K s.component_le s.component s.model
  let : (Source.starImage H K).Normal := s.star_component_normal
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  let : IsSimpleGroup (Source.starImage H K) := e.isSimpleGroup
  have hna : ¬ IsMulCommutative (Source.starImage H K) := by
    intro hc
    have hcomm : IsMulCommutative M22 := ⟨⟨fun x y => by
      obtain ⟨a, rfl⟩ := e.surjective x
      obtain ⟨b, rfl⟩ := e.surjective y
      exact (e.map_mul a b).symm.trans ((congrArg e (mul_comm' a b)).trans (e.map_mul b a))⟩⟩
    have hz : (⊤ : Subgroup M22) = ⊥ := (center_eq_top (G := M22)).symm.trans m22_center_eq_bot
    exact top_ne_bot hz
  apply centralizer_eq_bot_of_simple_two_quotient _ hna
  · apply isPGroup_quotient_of_sup_eq_top _ (Source.starImage H T) _ s.star_component_join_sylow
    change IsPGroup 2 ((T.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))
    rw [← s.sylow_eq]
    exact s.sylow.isPGroup'.map _
  · exact pCore_quotient_pCore_eq_bot 2

/-- The design action obtained by conjugating the normal component. -/
noncomputable def designHom : Source.Hstar H →* m22DesignAut := by
  let := s.star_component_normal
  exact M22ValueBound.Concrete.ambientHom (Source.starImage H K)
    (starCoordinates H K s.component_le s.component s.model)

theorem designHom_injective : Function.Injective s.designHom := by
  let := s.star_component_normal
  exact M22ValueBound.Concrete.ambientHom_injective _ _ s.star_component_centralizer

/-- Compatibility with the specified model on every intrinsic quotient element. -/
theorem designHom_component (q : K ⧸ pCore 2 K) :
    s.designHom (Components.componentStarEquiv H K s.component_le s.component q) =
      M22ValueBound.Concrete.inclusion (s.model q) := by
  let := s.star_component_normal
  rw [designHom, M22ValueBound.Concrete.ambientHom_apply_inner]
  simp [starCoordinates]

theorem designHom_map_component : (Source.starImage H K).map s.designHom =
    M22ValueBound.Concrete.inner := by
  let := s.star_component_normal
  exact M22ValueBound.Concrete.ambientHom_map_inner _ _

theorem designHom_range : s.designHom.range = M22ValueBound.Concrete.inner ∨
    s.designHom.range = ⊤ :=
  M22ValueBound.Concrete.intermediate_eq_inner_or_top _
    (s.designHom_map_component ▸ (Source.starImage H K).map_le_range s.designHom)
end Setup
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement
