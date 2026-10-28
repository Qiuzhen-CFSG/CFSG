module
public import Theory.GroupTheory.QuaternionCentralProductIndependentCubics
public import Theory.GroupTheory.QuaternionCentralProductNineAction.FactorSwap

/-!
# Factor interchange does not invert the cubic image

The independent cubic actor supported on the first quaternion factor is
carried by a factor interchange to an actor supported on the second factor.
If the two actors were inverse modulo the quaternion product, restriction
to the first factor would make its nontrivial cubic automorphism inner.
Inner quaternion automorphisms have square one, which is impossible.

Source: Aschbacher–Smith, §5.3.7, printed p.661 (PDF p.678).
-/

namespace Subgroup

private theorem quaternion_inner_cube_eq_one
    {D : Type*} [Group D] (model : D ≃* QuaternionGroup 2)
    (a : MulAut D) (ha : a ^ 3 = 1) (b : D) (hb : a = MulAut.conj b) : a = 1 := by
  have htable : ∀ x y : QuaternionGroup 2, x ^ 2 * y = y * x ^ 2 := by decide
  have ha2 : a ^ 2 = 1 := by
    rw [hb, ← map_pow]
    ext x
    change b ^ 2 * x * (b ^ 2)⁻¹ = x
    have hc : b ^ 2 * x = x * b ^ 2 := by
      apply model.injective
      simpa only [map_mul, map_pow] using htable (model b) (model x)
    rw [hc, mul_inv_cancel_right]
  have h := ha
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, ha2, one_mul] at h
  exact h

/-- Interchanging the factors cannot induce inversion on the image of the
independent cubic actors modulo their quaternion central product. -/
public theorem QuaternionIndependentCubics.not_inversion_of_factor_swap
    {G K : Type*} [Group G] [Finite G] [Group K]
    {B C : Subgroup G} (actors : QuaternionIndependentCubics B C)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (f : G →* K) (hker : f.ker = B ⊔ C)
    (s : G) (hswap : C.map (MulAut.conj s).toMonoidHom = B) :
    ∃ a : actors.A, f s * f a * (f s)⁻¹ ≠ (f a)⁻¹ := by
  refine ⟨actors.x, ?_⟩
  intro hinv
  let x : G := actors.x
  let y : G := s * x * s⁻¹
  have hyB : y ∈ centralizer (B : Set G) := by
    rw [← hswap]
    rintro _ ⟨c, hc, rfl⟩
    change (s*c*s⁻¹)*(s*x*s⁻¹) = (s*x*s⁻¹)*(s*c*s⁻¹)
    have hxc := actors.x_centralizes c hc
    change c * x = x * c at hxc
    calc
      _ = s * (c*x) * s⁻¹ := by group
      _ = s * (x*c) * s⁻¹ := by rw [hxc]
      _ = _ := by group
  have hyx : y * x ∈ B ⊔ C := by
    rw [← hker, MonoidHom.mem_ker]
    change f ((s*x*s⁻¹)*x) = 1
    rw [map_mul, map_mul, map_mul, map_inv]
    change (f s * f actors.x * (f s)⁻¹) * f actors.x = 1
    rw [hinv, inv_mul_cancel]
  have hnorm : B ≤ normalizer (C : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    exact fun b hb c hc => (hcomm b hb c hc).symm
  change y * x ∈ ((B ⊔ C : Subgroup G) : Set G) at hyx
  rw [coe_mul_of_left_le_normalizer_right B C hnorm] at hyx
  obtain ⟨b, hb, c, hc, hbc⟩ := hyx
  change b * c = y * x at hbc
  have hinner : actors.actionB actors.x = MulAut.conj (⟨b, hb⟩ : B) := by
    ext w
    rw [actors.actionB_apply]
    change x * (w : G) * x⁻¹ = b * (w : G) * b⁻¹
    have hxw : x * (w : G) * x⁻¹ ∈ B :=
      (mem_normalizer_iff.mp (actors.normalizes_left actors.x.property) w).mp w.property
    have hyw := hyB _ hxw
    have hcw := hcomm w w.property c hc
    calc
      _ = y * (x * (w : G) * x⁻¹) * y⁻¹ := by rw [← hyw, mul_inv_cancel_right]
      _ = (y*x) * (w : G) * (y*x)⁻¹ := by group
      _ = (b*c) * (w : G) * (b*c)⁻¹ := by rw [← hbc]
      _ = b * (c * (w : G) * c⁻¹) * b⁻¹ := by group
      _ = _ := by rw [← hcw, mul_inv_cancel_right]
  have hx3 : actors.x ^ 3 = 1 := by
    apply Subtype.ext
    exact actors.x_order ▸ pow_orderOf_eq_one (actors.x : G)
  exact actors.x_actionB_ne_one (quaternion_inner_cube_eq_one hB.some
    (actors.actionB actors.x) (by rw [← map_pow, hx3, map_one]) ⟨b, hb⟩ hinner)

end Subgroup
