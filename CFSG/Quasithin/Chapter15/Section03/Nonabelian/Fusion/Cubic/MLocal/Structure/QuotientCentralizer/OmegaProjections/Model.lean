module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.NaturalAction

/-!
# A fixed functional for a plane cubic in an S₃ subgroup

A nonidentity cubic fixing one of the two definite planes acts trivially on
that plane. An involution inverting it preserves the plane and fixes a
nonzero binary functional there. The cubic and that involution generate S₃,
so the functional is invariant under the whole subgroup.

Two small kernel-checked certificates verify the six-element generator
calculation and the invariant functional in the literal 72-element wreath
action. The extension from the two generators to an arbitrary homomorphism
is proved algebraically. This is the representation calculation needed to
distinguish the fully moving Omega factors from the definite-plane factors.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.53(1),
printed p.1146, and the setup of 15.3.60, printed p.1150.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure.OmegaProjections

local instance : MulDistribMulAction OrthogonalActor OrthogonalVector := orthogonalAction
private instance : DecidableEq OrthogonalActor :=
  (RegularWreathProduct.equivProd _ _).decidableEq
private instance : Fintype OrthogonalActor := Fintype.ofEquiv
  ((OrthogonalPlaneIndex → OrthogonalPlaneActor) × OrthogonalPlaneIndex)
  (RegularWreathProduct.equivProd _ _).symm

private def dot (u w : OrthogonalPlaneVector) : ZMod 2 :=
  u.toAdd 0 * w.toAdd 0 + u.toAdd 1 * w.toAdd 1

private theorem plane_actor_generators : ∀ x : OrthogonalPlaneActor, x ^ 3 = 1 → x ≠ 1 →
    ∃ t : OrthogonalPlaneActor, t ^ 2 = 1 ∧ t * x * t⁻¹ = x⁻¹ ∧
      ∀ z, z = 1 ∨ z = x ∨ z = x ^ 2 ∨ z = t ∨ z = x * t ∨ z = x ^ 2 * t := by
  decide +kernel

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 4000 in
private theorem plane_cubic_functional_certificate : ∀ (i : OrthogonalPlaneIndex) (a : OrthogonalActor),
    a ^ 3 = 1 → a ≠ 1 →
    (∀ w : OrthogonalVector, (∀ j, j ≠ i → w j = 1) → a • w = w) →
    ∀ b : OrthogonalActor, b ^ 2 = 1 → b * a * b⁻¹ = a⁻¹ →
    ∃ u : OrthogonalPlaneVector,
      (∃ w : OrthogonalVector, dot u (w i) ≠ 0) ∧
      (∀ w : OrthogonalVector, dot u ((a • w) i) = dot u (w i)) ∧
      (∀ w : OrthogonalVector, dot u ((b • w) i) = dot u (w i)) := by
  decide +kernel

private def functional (i : OrthogonalPlaneIndex) (u : OrthogonalPlaneVector) :
    OrthogonalVector →* Multiplicative (ZMod 2) where
  toFun w := Multiplicative.ofAdd (dot u (w i))
  map_one' := by change dot u 1 = 0; simp [dot]
  map_mul' v w := by
    change dot u (v i * w i) = dot u (v i) + dot u (w i)
    simp only [dot, toAdd_mul, Pi.add_apply]
    ring

/-- An S₃ action containing a nonidentity cubic that fixes a definite plane
has a nonzero invariant binary functional. -/
theorem invariant_functional_of_plane_cubic (f : OrthogonalPlaneActor →* OrthogonalActor)
    (x : OrthogonalPlaneActor) (hx : x ^ 3 = 1) (hne : f x ≠ 1)
    (i : OrthogonalPlaneIndex)
    (hfix : ∀ w : OrthogonalVector, (∀ j, j ≠ i → w j = 1) → f x • w = w) :
    ∃ χ : OrthogonalVector →* Multiplicative (ZMod 2),
      (∃ w, χ w ≠ 1) ∧ ∀ y w, χ (f y • w) = χ w := by
  have hxne : x ≠ 1 := by intro h; exact hne (by rw [h, map_one])
  obtain ⟨t, ht, htx, hgen⟩ := plane_actor_generators x hx hxne
  have hfx : f x ^ 3 = 1 := by rw [← map_pow, hx, map_one]
  have hft : f t ^ 2 = 1 := by rw [← map_pow, ht, map_one]
  have hftx : f t * f x * (f t)⁻¹ = (f x)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, htx, map_inv]
  obtain ⟨u, ⟨w, hw⟩, hxu, htu⟩ := plane_cubic_functional_certificate i (f x) hfx hne hfix (f t) hft hftx
  refine ⟨functional i u, ⟨w, hw⟩, ?_⟩
  intro y v
  change dot u ((f y • v) i) = dot u (v i)
  rcases hgen y with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [map_one, one_smul]
  · exact hxu v
  · simp only [pow_two, map_mul, mul_smul, hxu]
  · exact htu v
  · simp only [map_mul, mul_smul, hxu, htu]
  · simp only [pow_two, map_mul, mul_smul, hxu, htu]

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure.OmegaProjections
