module
public import Theory.SpecificGroups.SymplecticFour.NaturalScalarCubic
public import Theory.Representation.AlternatingFiveLinearTwoObstruction

/-!
# The natural action on the fixed spaces of the two local cores

The point local fixes the entire fixed space of its own two-core. In the
plane local, a cubic quotient element fixes no nonzero vector in that core
fixed space: the latter is the natural plane for the actual SL₂ quotient.

These statements retain the literal residual core, rather than the larger
parabolic core. They supply the natural projection calculation for the
original A₅ source's moved-cover obstruction.
-/

public noncomputable section
open Matrix Subgroup
namespace Theory.SpecificGroups.SymplecticFour.CoreFixedCubic
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The point residual fixes every natural vector fixed by its whole two-core. -/
theorem point_fixed_of_core_fixed (hF : Nat.card F = 4)
    (v : Vector F) (hv : ∀ q ∈ (pointLocal (F := F)).pCoreIn 2, q • v = v)
    (b : pointLocal (F := F)) : b.val • v = v := by
  have hcore : (pointLocal (F := F)).pCoreIn 2 = pointRadicalAmbient := by
    unfold Subgroup.pCoreIn
    rw [pointLocal_core_eq (n := 2) hF (by decide)]
  have hp : v ∈ point F := NaturalScalarCubic.point_radical_fixed v (by
    rwa [hcore] at hv)
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hp
  rw [← ha]
  change toLinear b.val (a • e 0) = a • e 0
  rw [map_smul]
  exact congrArg (a • ·) ((mem_pointLocal_iff_fixed b.val).mp b.property)

/-- A cubic element of the literal plane quotient has no nonzero natural
fixed vector centralized by the entire plane-local two-core. -/
theorem plane_cubic_fixed_eq_zero (hF : Nat.card F = 4)
    (b : planeLocal (F := F)) (hb : orderOf (Plane.quotientMap b) = 3)
    (v : Vector F) (hv : ∀ q ∈ (planeLocal (F := F)).pCoreIn 2, q • v = v)
    (hfix : b.val • v = v) : v = 0 := by
  have hcore : (planeLocal (F := F)).pCoreIn 2 = planeRadicalAmbient := by
    unfold Subgroup.pCoreIn
    rw [planeLocal_core_eq (n := 2) hF (by decide)]
  have hp : v ∈ plane F := NaturalScalarCubic.plane_radical_fixed v (by
    rwa [hcore] at hv)
  have hp' : ∀ i : Fin 2, v (.inr i) = 0 := hp
  have hfirst : (fun i : Fin 2 => v (.inl i)) = 0 := by
    apply Matrix.SL2.cubic_fixed_eq_zero (Plane.quotientMap b) hb
    funext i
    have hh := congrFun hfix (.inl i)
    simpa only [smul_eq_mulVec, mulVec, dotProduct, Fintype.sum_sum_type,
      hp', mul_zero, Finset.sum_const_zero, add_zero, Plane.quotientMap_val,
      Matrix.toBlocks₁₁, Matrix.of_apply] using hh
  funext i
  rcases i with i | i
  · exact congrFun hfirst i
  · exact hp i

end Theory.SpecificGroups.SymplecticFour.CoreFixedCubic
