module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Detecting extension cores from their action on a local quotient

A normal p-subgroup of an overgroup acts trivially on a normal local subgroup
modulo that local subgroup's p-core: the commutators lie in the intersection
of the ambient core with the local subgroup. If p-elements with this trivial
action belong to the local subgroup, characteristic-normal transitivity
identifies the two cores.

The join version proves normality inside the join from the supplement's
normalizing action. All core comparisons use the literal maps into the same
ambient group. The detection premise is a separate automorphism calculation;
these transfer results do not assert it for symplectic groups.

Source: the elementary normal-subgroup argument underlying the core identity
in Aschbacher--Smith, F.1.12, printed p.264 of `refs/quasithin.pdf`.
-/

public section

open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

/-- A normal p-subgroup acts trivially on the quotient of a normal subgroup
by its own p-core. -/
theorem normal_pCore_commutator_mem (p : ℕ) (L : Subgroup G) [L.Normal]
    {g : G} (hg : g ∈ pCore p G) (l : L) :
    ⁅g, l.val⁆ ∈ (pCore p L).map L.subtype := by
  have hL : ⁅g, l.val⁆ ∈ L :=
    L.mul_mem ((inferInstance : L.Normal).conj_mem l.val l.property g) (L.inv_mem l.property)
  have hR : ⁅g, l.val⁆ ∈ pCore p G := by
    have h := commutator_mem_commutator hg l.property
    exact (commutator_le_left (pCore p G) L) h
  have hle : (pCore p G).subgroupOf L ≤ pCore p L :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
  exact ⟨⟨⁅g, l.val⁆, hL⟩, hle hR, rfl⟩

/-- The core identity follows if p-elements acting trivially on the local
core quotient lie in the normal local subgroup. -/
theorem map_pCore_eq_of_quotient_action_detection (p : ℕ) (L : Subgroup G) [L.Normal]
    (hdetect : ∀ g : G, (∃ n : ℕ, g ^ p ^ n = 1) →
      (∀ l : L, ⁅g, l.val⁆ ∈ (pCore p L).map L.subtype) → g ∈ L) :
    (pCore p L).map L.subtype = pCore p G := by
  have hRL : pCore p G ≤ L := by
    intro g hg
    obtain ⟨n, hn⟩ := pCore_isPGroup.exists_pow_pow_eq_one (⟨g, hg⟩ : pCore p G)
    exact hdetect g ⟨n, congrArg Subtype.val hn⟩
      (fun l => normal_pCore_commutator_mem p L hg l)
  apply le_antisymm
  · exact le_sSup ⟨ConjAct.normal_of_characteristic_of_normal,
      pCore_isPGroup.map L.subtype⟩
  · have hle : (pCore p G).subgroupOf L ≤ pCore p L :=
      le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
    simpa only [map_subgroupOf_eq_of_le hRL] using map_mono (f := L.subtype) hle

/-- The same criterion in a join, with normality proved inside the join
from the normalizing action of the supplement. -/
theorem join_pCore_eq_of_quotient_action_detection (p : ℕ) (L S : Subgroup G)
    (hnorm : S ≤ normalizer (L : Set G))
    (hdetect : ∀ g : G, g ∈ L ⊔ S → (∃ n : ℕ, g ^ p ^ n = 1) →
      (∀ l : L, ⁅g, l.val⁆ ∈ (pCore p L).map L.subtype) → g ∈ L) :
    (pCore p (L ⊔ S : Subgroup G)).map (L ⊔ S).subtype = (pCore p L).map L.subtype := by
  let H : Subgroup G := L ⊔ S
  let K := L.subgroupOf H
  have hLH : L ≤ H := le_sup_left
  let : K.Normal := normal_subgroupOf_iff_le_normalizer hLH |>.mpr
    (sup_le L.le_normalizer hnorm)
  let e : K ≃* L := subgroupOfEquivOfLe hLH
  have hmaps : ((pCore p K).map K.subtype).map H.subtype =
      (pCore p L).map L.subtype := by
    rw [← pCore_map_iso p e, map_map, map_map]
    rfl
  have hcore : (pCore p K).map K.subtype = pCore p H := by
    apply map_pCore_eq_of_quotient_action_detection
    intro g hg hc
    apply hdetect g.val g.property
    · obtain ⟨n, hn⟩ := hg
      exact ⟨n, congrArg Subtype.val hn⟩
    · intro l
      have hx := mem_map_of_mem H.subtype (hc (e.symm l))
      rw [hmaps] at hx
      exact hx
  rw [← hcore]
  exact hmaps
end Subgroup
