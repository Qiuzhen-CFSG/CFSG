module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.CubicSylowCentralizer
public import Theory.GroupTheory.PCoreCharacteristicCentralizer
/-!
# Faithful cubic action and the nontrivial Borel core of a short block

For a centerless short group, a cubic subgroup acts faithfully on any full
Sylow two-subgroup: its kernel fixes that Sylow and hence the entire short
group. Shortness also makes the Sylow nontrivial. The corresponding torus
normalizer join therefore has nontrivial two-core.

Source: Aschbacher–Smith 10.2.3(4), printed p.747. No special64 model or
assumption that the core equals the moved module is needed.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- A cubic subgroup of a centerless short group acts faithfully on its Sylow. -/
theorem IsShort.cubic_sylow_action_faithful (K P D : Subgroup G) (hK : IsShort K)
    (hP : Chapter1.IsSylowIn 2 P K) (hz : center K = ⊥)
    (hDK : D ≤ K) (hD : Nat.card D = 3) : D ⊓ centralizer (P : Set G) = ⊥ := by
  let A := D ⊓ centralizer (P : Set G)
  have hp : IsPGroup 3 A := (IsPGroup.of_card (n := 1) (by simpa using hD)).to_le inf_le_left
  have ha : A ≤ centralizer (K : Set G) := IsShort.centralizes_of_cubic_sylow_fixed
    K P A hK hP hp ((inf_le_left.trans hDK).trans K.le_normalizer) inf_le_right
  apply bot_unique
  intro x hx
  have hxK := hDK hx.1
  have hc : (⟨x,hxK⟩ : K) ∈ center K := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (ha hx y y.property)
  rw [hz,mem_bot] at hc
  exact mem_bot.mpr (congrArg K.subtype hc)

omit [Finite G] in
/-- A full Sylow two-subgroup of a short group is nontrivial. -/
theorem IsShort.ambient_sylow_ne_bot (K P : Subgroup G) (hK : IsShort K)
    (hP : Chapter1.IsSylowIn 2 P K) : P ≠ ⊥ := by
  obtain ⟨Q,hQ⟩ := hP
  have hUP : (blockU K).map K.subtype ≤ P :=
    (map_mono (blockU_le_core.trans (pCore_isPGroup.le_sylow_of_normal Q))).trans_eq hQ
  intro he
  have hu : blockU K = ⊥ := (map_eq_bot_iff_of_injective _ K.subtype_injective).mp
    (bot_unique (hUP.trans he.le))
  have hh := hK.irreducible.1
  rw [hu,bot_inf_eq] at hh
  exact lt_irrefl _ hh

omit [Finite G] in
private theorem two_group_borel_core_ne_bot (P D : Subgroup G) (hP : IsPGroup 2 P) (hne : P ≠ ⊥)
    (hDP : D ≤ normalizer (P : Set G)) : pCore 2 (P ⊔ D : Subgroup G) ≠ ⊥ := by
  have hp : P ≤ (P ⊔ D : Subgroup G).pCoreIn 2 :=
    le_pCoreIn_of_normalizes hP le_sup_left (sup_le P.le_normalizer hDP)
  intro he
  apply hne
  apply bot_unique
  exact hp.trans (by change (pCore 2 (P ⊔ D : Subgroup G)).map _ ≤ ⊥; simp [he])
omit [Finite G] in
/-- The literal Sylow–torus Borel of a short group has nontrivial two-core. -/
theorem IsShort.borel_core_ne_bot (K P D : Subgroup G) (hK : IsShort K)
    (hP : Chapter1.IsSylowIn 2 P K) (hDP : D ≤ normalizer (P : Set G)) :
    pCore 2 (P ⊔ D : Subgroup G) ≠ ⊥ :=
  two_group_borel_core_ne_bot P D (Chapter1.isSylowIn_iff.mp hP).1
    (IsShort.ambient_sylow_ne_bot K P hK hP) hDP
end CFSG.Quasithin.ChapterC
