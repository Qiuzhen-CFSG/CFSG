module

public import Theory.GroupTheory.QuaternionBinaryCentralExtension.FixedLifts
public import Theory.Mathieu.M12.SmallParabolicPair.FirstCore

/-!
# A commuting-lift relation in every central extension of M₁₂

The first parabolic normalizes a marked quaternion factor, so its full
preimage centralizes every lift of z. The second-parabolic cubic moves z
to v while normalizing the marked elementary eight. Conjugating the first
commutation statement therefore makes every lift of v commute with every
lift of that eight, in particular with every lift of `third`.

This is the fusion constraint used by the relative first-parabolic multiplier
bound. It holds for arbitrary central kernels, without assuming that they
have exponent two or that the extension is perfect.
Source: Aschbacher–Smith I.1.3(1), printed p.407, citing GLS3 §6.1;
the literal local geometry is the M₁₂ pair in 14.2.21, printed p.988.
-/

namespace Sporadic.Mathieu.SchurMultipliers.M12Upper
open M12SmallPair Subgroup
variable {E : Type*} [Group E]

/-- Quaternion-factor normality forces every lift of z to centralize the
preimage of its centralizer in M12. -/
public theorem commute_lifts_z_firstParabolic
    (f : E →* M12) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    (a b : E) (ha : f a = z) (hb : f b ∈ firstParabolic) : Commute a b := by
  let e : leftFactor ≃* QuaternionGroup 2 :=
    (MonoidHom.ofInjective leftEmbedding_injective).symm
  have hzQ : z ∈ leftFactor := ⟨.a 2, by decide +kernel⟩
  have hxQ : f a ∈ leftFactor := ha ▸ hzQ
  apply (f.commute_lift_of_quaternion_normalizer hf hk leftFactor e b a
    (firstParabolic_normalizes_left hb) hxQ ?_).symm
  apply e.symm.injective
  rw [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  change f a = leftEmbedding (.a 2)
  rw [ha]
  decide +kernel

/-- The second-parabolic cubic moves z to v and normalizes the elementary
 eight. Thus every lift of v centralizes the preimage of that eight. -/
public theorem commute_lifts_v_elementary
    (f : E →* M12) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    (a b : E) (ha : f a = v) (hb : f b ∈ elementary) : Commute a b := by
  obtain ⟨c, hc⟩ := hf movingActor
  have hca : f (c⁻¹ * a * c) = z := by
    simp only [map_mul, map_inv, hc, ha]
    rw [← movingActor_conjugates_z]
    group
  have hcb : f (c⁻¹ * b * c) ∈ firstParabolic := by
    apply core_le_firstParabolic
    apply elementary_le_core
    simpa only [map_mul, map_inv, hc, inv_inv] using
      (mem_normalizer_iff.mp
        ((normalizer (elementary : Set M12)).inv_mem movingActor_normalizes_elementary)
        (f b)).mp hb
  have h := commute_lifts_z_firstParabolic f hf hk _ _ hca hcb
  apply Commute.of_map (MulAut.conj c⁻¹).injective
  simpa only [MulAut.conj_apply, inv_inv] using h

/-- The commuting-lift relation needed by the relative first-parabolic bound. -/
public theorem commute_lifts_v_third
    (f : E →* M12) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    (a b : E) (ha : f a = v) (hb : f b = third) : Commute a b := by
  apply commute_lifts_v_elementary f hf hk a b ha
  rw [hb]
  exact subset_closure (by simp)

end Sporadic.Mathieu.SchurMultipliers.M12Upper
