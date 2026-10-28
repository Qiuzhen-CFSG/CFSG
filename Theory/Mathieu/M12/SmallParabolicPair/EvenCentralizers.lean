module

public import Theory.Mathieu.M12.SmallParabolicPair

/-!
# Self-centralizing two-cores of the marked M₁₂ parabolics

The first parabolic's quaternion core is already identified with its intrinsic
O₂. An element centralizing the marked elementary eight centralizes z and
normalizes the natural four, hence lies in the common Sylow subgroup. Its
centralizer there is the eight itself. Normality of the eight in the second
parabolic then makes that parabolic's intrinsic O₂ self-centralizing.

Source: Aschbacher–Smith, Theorem 0.1.2(5), pp.3–4 and 481–482; the concrete
marked pair is the model used in Lemma 14.2.21, p.988. Exhaustive local
coverage is a separate calculation.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Sporadic.Mathieu.M12SmallPair

theorem centralizer_elementary_eq :
    centralizer (elementary : Set M12) = elementary := by
  apply le_antisymm
  · intro g hg
    rw [← sylowCandidate_centralizer_elementary]
    refine ⟨⟨?_, ?_⟩, hg⟩
    · exact mem_centralizer_singleton_iff.mpr
        (hg z (natural_le_elementary z_mem_natural)).symm
    · exact centralizer_le_normalizer (natural : Set M12)
        (centralizer_le natural_le_elementary hg)
  · exact le_centralizer_iff.mpr (fun x hx y hy =>
      congrArg Subtype.val (mul_comm (⟨y, hy⟩ : elementary) ⟨x, hx⟩))

theorem firstParabolic_pCore_selfCentralizing :
    centralizer (pCore 2 firstParabolic : Set firstParabolic) ≤
      pCore 2 firstParabolic := by
  rw [← core_subgroupOf_eq_pCore]
  intro g hg
  have hc : (g : M12) ∈ centralizer (core : Set M12) := by
    intro x hx
    exact congrArg Subtype.val (hg ⟨x, core_le_firstParabolic hx⟩ hx)
  have hz : (g : M12) ∈ distinguished := by
    rw [← firstParabolic_centralizer_core]
    exact ⟨g.property, hc⟩
  exact natural_le_core (distinguished_le_natural hz)

theorem elementary_subgroupOf_le_pCore :
    elementary.subgroupOf secondParabolic ≤ pCore 2 secondParabolic := by
  apply le_sSup
  refine ⟨inferInstance, ?_⟩
  exact (commonSylow.isPGroup'.to_le elementary_le_sylowCandidate).of_equiv
    (subgroupOfEquivOfLe elementary_le_secondParabolic).symm

theorem secondParabolic_pCore_selfCentralizing :
    centralizer (pCore 2 secondParabolic : Set secondParabolic) ≤
      pCore 2 secondParabolic := by
  intro g hg
  apply elementary_subgroupOf_le_pCore
  change (g : M12) ∈ elementary
  rw [← centralizer_elementary_eq]
  intro x hx
  exact congrArg Subtype.val
    (hg ⟨x, elementary_le_secondParabolic hx⟩ (elementary_subgroupOf_le_pCore hx))

end Sporadic.Mathieu.M12SmallPair
