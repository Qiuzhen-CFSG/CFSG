module
public import Theory.GroupTheory.Commutator.NormalClosure

/-!
# Normal subgroups below a quadratic normal generator

If P normally generates G and acts quadratically on a normal subgroup U,
then every normal subgroup Q contained in P centralizes [U,G]. Quadraticity
first makes P centralize [U,Q] and makes [Q,P] centralize U. Normal closure
extends both statements to G; the three-subgroup lemma gives the result.

Source application: the Baumann step in MS93 (5.1), printed p.913.
Glauberman.BaumannQuadraticLayer applies this to the whole two-core.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- A normal subgroup below a quadratic normal generator fixes the entire moved layer. -/
theorem core_centralizes_moved_of_quadratic_normal_generation
    (U Q P : Subgroup G) [U.Normal] [Q.Normal]
    (hQP : Q ≤ P) (hgen : normalClosure (P : Set G) = ⊤)
    (hquad : ⁅⁅U,P⁆,P⁆ = ⊥) : ⁅U,(⊤ : Subgroup G)⁆ ≤ centralizer (Q : Set G) := by
  have hUQP : ⁅⁅U,Q⁆,P⁆ = ⊥ := bot_unique
    ((commutator_mono (commutator_mono le_rfl hQP) le_rfl).trans_eq hquad)
  have hUPQ : ⁅⁅U,P⁆,Q⁆ = ⊥ := bot_unique
    ((commutator_mono le_rfl hQP).trans_eq hquad)
  have hQPU : ⁅⁅Q,P⁆,U⁆ = ⊥ := by
    apply commutator_commutator_eq_bot_of_rotate
    · simpa only [commutator_comm P U] using hUPQ
    · simpa only [commutator_comm Q U] using hUQP
  have hUQG : ⁅⁅U,Q⁆,(⊤ : Subgroup G)⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    rw [←hgen]
    exact normalClosure_le_normal
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hUQP))
  have hQGU : ⁅⁅Q,(⊤ : Subgroup G)⁆,U⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [←hgen]
    exact commutator_normalClosure_le_of_normal Q P (centralizer (U : Set G))
      (commutator_eq_bot_iff_le_centralizer.mp hQPU)
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply commutator_commutator_eq_bot_of_rotate
  · simpa only [commutator_comm (⊤ : Subgroup G) Q] using hQGU
  · simpa only [commutator_comm Q U] using hUQG
end Subgroup
