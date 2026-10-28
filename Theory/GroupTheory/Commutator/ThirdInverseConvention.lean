module

public import Theory.GroupTheory.Commutator.ThirdHom

/-!
# Inverse-first third commutators

When the third commutator is central, its homomorphism is unchanged if both
commutators use the inverse-first convention. Inverting both inputs of a
central commutator leaves it unchanged; the two inner input inversions cancel
by multiplicativity of the third commutator.

This is standard class-three group calculus, independent of coordinates.
-/

open scoped commutatorElement IsMulCommutative

namespace Subgroup
variable {G : Type*} [Group G]

/-- Simultaneously inverting both inputs preserves a central commutator. -/
public theorem commutator_inv_inv_of_mem_center (x y : G)
    (hc : ⁅x,y⁆ ∈ center G) : ⁅x⁻¹,y⁻¹⁆ = ⁅x,y⁆ := by
  rw [commutatorElement_inv_left, commutatorElement_inv_left]
  have hh := mem_center_iff.mp hc
  rw [hh y⁻¹]
  simp only [mul_assoc, inv_mul_cancel, mul_one]
  rw [← hh x, inv_mul_cancel_left]

/-- The inverse-first third commutator is a homomorphism in all three inputs. -/
public theorem exists_inverse_first_third_commutator_hom
    (hc : ⁅_root_.commutator G, (⊤ : Subgroup G)⁆ ≤ center G) :
    ∃ F : G →* (G →* (G →* center G)), ∀ x y z,
      (F x y z : G) = (x⁻¹*y⁻¹*x*y)⁻¹*z⁻¹*(x⁻¹*y⁻¹*x*y)*z := by
  obtain ⟨F, hF⟩ := exists_third_commutator_hom hc
  refine ⟨F, ?_⟩
  intro x y z
  have hc' : ⁅⁅x⁻¹,y⁻¹⁆,z⁆ ∈ center G :=
    hc (commutator_mem_commutator
      (commutator_mem_commutator (mem_top _) (mem_top _)) (mem_top _))
  calc
    (F x y z : G) = (F x⁻¹ y⁻¹ z : G) := by simp
    _ = ⁅⁅x⁻¹,y⁻¹⁆,z⁆ := hF _ _ _
    _ = ⁅⁅x⁻¹,y⁻¹⁆⁻¹,z⁻¹⁆ := (commutator_inv_inv_of_mem_center _ _ hc').symm
    _ = _ := by simp only [commutatorElement_def, inv_inv]

end Subgroup
