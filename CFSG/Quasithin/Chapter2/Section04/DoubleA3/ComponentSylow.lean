module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.SourceSetup
public import Theory.GroupTheory.SylowNormalRestriction
public import Mathlib.GroupTheory.IndexNormal

/-!
# The actual component Sylow in the paired cubic branch

The original Thompson subgroup R has index two in S₁, acts naturally
on K ≅ A₆, and the marked x in S₁ acts outside the natural S₆.
The other coset thus consists entirely of nonnatural actors. Since
inner actors are natural, S₁ ∩ K equals R ∩ K. Normal Sylow restriction
then gives the required Sylow subgroup of the literal component.

Source: Aschbacher–Smith 2.4.36(1), printed p.549,
combined manuscript, 1 March 2004.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.DoubleA3
open AlternatingSix.ShadowLocal
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The actual component intersection is Sylow once the original Thompson
subgroup has index two in the marked centralizer Sylow. -/
theorem SourceComponentGeometry.exists_component_sylow
    {d : MinimalBlockSetup M} (c : SourceComponentGeometry d)
    (hi : (((sourceR d).subgroupOf (involutionCentralizer c.z)).subgroupOf
      (c.S₁ : Subgroup (involutionCentralizer c.z))).index = 2)
    (hx : c.x ∈ (c.S₁ : Subgroup (involutionCentralizer c.z))) :
    ∃ P : Sylow 2 c.K, (P : Subgroup c.K).map c.K.subtype =
      (sourceR d).subgroupOf (involutionCentralizer c.z) ⊓ c.K := by
  let R := (sourceR d).subgroupOf (involutionCentralizer c.z)
  let S : Subgroup (involutionCentralizer c.z) := c.S₁
  let A := conjugationAction c.K c.componentEquiv
  have hK : c.K.map A ≤ natural := (conjugationAction_map_inner c.K c.componentEquiv).le.trans inner_le_natural
  have hxR : c.x ∉ R := fun h => c.outside_natural
    (c.natural_thompson (mem_map_of_mem A h))
  have he : S ⊓ c.K = R ⊓ c.K := by
    apply le_antisymm
    · intro a ha
      refine ⟨?_, ha.2⟩
      by_contra hnot
      have hmul : a * c.x ∈ R := by
        have hh := (Subgroup.mul_mem_iff_of_index_two (H := R.subgroupOf S)
          (a := (⟨a, ha.1⟩ : S)) (b := (⟨c.x, hx⟩ : S)) hi).mpr (by
            change (a ∈ R ↔ c.x ∈ R)
            exact ⟨fun h => False.elim (hnot h), fun h => False.elim (hxR h)⟩)
        exact hh
      have haN : A a ∈ natural := hK (mem_map_of_mem A ha.2)
      have hmulN : A a * A c.x ∈ natural := by
        rw [← map_mul]
        exact c.natural_thompson (mem_map_of_mem A hmul)
      exact c.outside_natural ((natural.mul_mem_cancel_left haN).mp hmulN)
    · exact inf_le_inf_right _ c.thompson_sylow
  obtain ⟨P, hP⟩ := c.S₁.exists_sylow_map_eq_inf_of_normal c.K
  exact ⟨P, hP.trans he⟩

end CFSG.Quasithin.Chapter2.DoubleA3
