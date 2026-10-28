module
public import Theory.SpecificGroups.ReeF4.SmallCompletion.Native
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Octagon.WeylGroup.Rotation

/-!
# The actual marked Ree reflections

The two fixed orbit words belong to their original parabolics and lie outside
the Borel. Their product has eighth power one in the native group: the known
quotient relation places that power in the torus, while the constant-parameter
Weyl subgroup meets the torus trivially. This supplies the literal model-side
relation for comparison of completions, without using a quotient relation as
if it were already a relation in an arbitrary completion.

Source: GLS3 2.3.2–4 and Aschbacher–Smith F.4.10,16, pp.279,282.
-/

@[expose] public noncomputable section
namespace ReeF4.SmallCompletion
open Subgroup Parabolics LargeLocalSeeds Parabolics.Binary.FixedGeometry
open SectionGeometry.BNPair
attribute [local instance] borel_inf_normalizerWords_normal

/-- The original orbit word as an element of its native endpoint. -/
def reflection (m : ℕ) (s : Side) : parabolic m s :=
  ⟨weylLift m s, seed_le_parabolic m s (weylLift_mem_seed m s)⟩

theorem reflection_sq (m : ℕ) (s : Side) : reflection m s ^ 2 = 1 :=
  Subtype.ext (weylLift_sq m s)

/-- Each marked involution is outside the full Borel. -/
theorem reflection_not_mem_borel (m : ℕ) (s : Side) :
    (reflection m s).val ∉ borel m := by
  intro hs
  obtain ⟨b,hb,hout⟩ := weylLift_borel_conjugation_witness m s
  exact hout (mul_mem (mul_mem hs hb) hs)

/-- The native lifts, not only their Weyl classes, satisfy the octagon relation. -/
theorem reflection_product_eight (m : ℕ) :
    ((reflection m .linear).val * (reflection m .suzuki).val)^8 = 1 := by
  have h := MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.MarkedWeyl.relativeRotation_pow_eight m
  have he : QuotientGroup.mk' _ ((simpleLift m .linear * simpleLift m .suzuki)^8) =
      (1 : WeylQuotient m) := by
    simpa only [map_pow,map_mul,simpleReflection] using h
  have ht : (weylLift m .linear * weylLift m .suzuki)^8 ∈ fixedTorus m := by
    rw [←borel_inf_normalizerWords]
    exact (QuotientGroup.eq_one_iff
      ((simpleLift m .linear * simpleLift m .suzuki)^8)).mp he
  exact (Subgroup.disjoint_def.mp
    (CentralCovers.OddPrimary.Order.fixedTorus_disjoint_weylSubgroup m)) ht
      (pow_mem (mul_mem (weylLift_mem_weylSubgroup m .linear)
        (weylLift_mem_weylSubgroup m .suzuki)) 8)
end ReeF4.SmallCompletion
