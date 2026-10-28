module

public import Theory.Mathieu.M12.SmallParabolicPair.Actions

/-!
# Marked centralizers inside the M₁₂ quaternion core

Each embedded quaternion factor normalizes the natural four, so the core
and its elementary eight lie in the intersection of the two parabolics.
The quaternion coordinates show that the elementary eight is self-centralizing
inside the core, and that the core's center consists of the identity and the
marked involution. These statements do not identify the core with O₂(H) or
assert that the parabolic intersection is Sylow.

Source: Aschbacher–Smith, Hypothesis 14.2.1 and Lemma 14.2.21, pp.981, 988.
-/

@[expose] public section
open scoped IsMulCommutative
namespace Sporadic.Mathieu.M12SmallPair
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

private theorem normalizes_natural_of_conjugates (g : M12)
    (h : ∀ i : Fin 4, let w : M12 := ![1,z,v,z*v] i
      g * w * g⁻¹ = 1 ∨ g * w * g⁻¹ = z ∨
        g * w * g⁻¹ = v ∨ g * w * g⁻¹ = z*v) : g ∈ secondParabolic := by
  apply Subgroup.mem_normalizer_fintype
  intro w hw
  change w ∈ natural at hw
  change _ ∈ natural
  rw [mem_natural] at hw ⊢
  rcases hw with rfl | rfl | rfl | rfl
  · exact h 0
  · exact h 1
  · exact h 2
  · exact h 3

theorem core_le_secondParabolic : core ≤ secondParabolic := by
  apply sup_le
  · rintro g ⟨q,rfl⟩
    apply normalizes_natural_of_conjugates
    have h : ∀ q : QuaternionGroup 2, ∀ i : Fin 4,
        let g := leftEmbedding q
        let w : M12 := ![1,z,v,z*v] i
        g * w * g⁻¹ = 1 ∨ g * w * g⁻¹ = z ∨
          g * w * g⁻¹ = v ∨ g * w * g⁻¹ = z*v := by decide +kernel
    exact h q
  · rintro g ⟨q,rfl⟩
    apply normalizes_natural_of_conjugates
    have h : ∀ q : QuaternionGroup 2, ∀ i : Fin 4,
        let g := rightEmbedding q
        let w : M12 := ![1,z,v,z*v] i
        g * w * g⁻¹ = 1 ∨ g * w * g⁻¹ = z ∨
          g * w * g⁻¹ = v ∨ g * w * g⁻¹ = z*v := by decide +kernel
    exact h q

theorem core_le_sylowCandidate : core ≤ sylowCandidate :=
  le_inf core_le_firstParabolic core_le_secondParabolic

theorem elementary_le_sylowCandidate : elementary ≤ sylowCandidate :=
  elementary_le_core.trans core_le_sylowCandidate

theorem core_centralizer_elementary :
    core ⊓ Subgroup.centralizer (elementary : Set M12) = elementary := by
  apply le_antisymm
  · rintro g ⟨hg,hc⟩
    obtain ⟨q,r,rfl⟩ := (mem_core g).mp hg
    have hv := hc v (natural_le_elementary v_mem_natural)
    have ht := hc third (Subgroup.subset_closure (by simp))
    have h : ∀ q r : QuaternionGroup 2,
        let g := leftEmbedding q * rightEmbedding r
        v * g = g * v → third * g = g * third →
          ∃ a : ElementaryCoordinates, elementaryEmbedding a = g := by
      decide +kernel
    rw [elementary_eq_range]
    exact h q r hv ht
  · intro g hg
    refine ⟨elementary_le_core hg, ?_⟩
    intro x hx
    exact congrArg Subtype.val (mul_comm (⟨x,hx⟩ : elementary) ⟨g,hg⟩)

theorem core_center_mem (g : core) :
    g ∈ Subgroup.center core ↔ (g : M12) = 1 ∨ (g : M12) = z := by
  rw [coreQuaternionData.center_eq]
  exact factors_intersection_mem g

end Sporadic.Mathieu.M12SmallPair
