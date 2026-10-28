module

public import Theory.GroupTheory.SpecificGroups.QuaternionEightAut

/-!
# Cubic differences generate a quaternion factor

A kernel-checked table shows that every element of Q₈ is a product of two
differences for any nonidentity cubic automorphism. Transport through a
quaternion model gives the ambient normal-subgroup containment used in the
residual product calculation. The table encodes automorphisms by generator
images, following `QuaternionEightAut.lean`.

Source: Aschbacher–Smith, Lemma 14.2.21, printed p.988 (PDF p.1005).
-/

namespace QuaternionGroup
private abbrev Q := QuaternionGroup 2
private def pairMap (p : Q × Q) : Q → Q
  | a i => p.1 ^ i.val
  | xa i => p.2 * p.1 ^ i.val
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem cubic_table : ∀ p : Q × Q,
    (∀ x, pairMap p (pairMap p (pairMap p x)) = x) →
    (∃ x, pairMap p x ≠ x) →
    ∀ z, ∃ u v, z = (u⁻¹ * pairMap p u) * (v⁻¹ * pairMap p v) := by
  decide

private theorem pairMap_aut (e : MulAut Q) (x : Q) :
    pairMap (e (a 1), e (xa 0)) x = e x := by
  cases x with
  | a i =>
    change (e (a 1)) ^ i.val = e (a i)
    rw [← map_pow, a_one_pow, ZMod.natCast_zmod_val]
  | xa i =>
    change e (xa 0) * (e (a 1)) ^ i.val = e (xa i)
    rw [← map_pow, ← map_mul, a_one_pow, ZMod.natCast_zmod_val, xa_mul_a, zero_add]

/-- Every quaternion is a product of two differences of a nontrivial cubic action. -/
public theorem eq_mul_cubic_differences_two (e : MulAut (QuaternionGroup 2))
    (he : e^3=1) (hne : e≠1) (z : QuaternionGroup 2) :
    ∃ u v, z = (u⁻¹ * e u) * (v⁻¹ * e v) := by
  have hc (x : Q) : e (e (e x)) = x := by
    simpa [pow_succ, MulAut.mul_apply] using DFunLike.congr_fun he x
  have hn : ∃ x, e x ≠ x := by
    by_contra! h
    exact hne (MulEquiv.ext h)
  simpa only [pairMap_aut] using cubic_table (e (a 1), e (xa 0))
    (by simpa only [pairMap_aut] using hc) (by simpa only [pairMap_aut] using hn) z

/-- A nontrivial cubic automorphism of any quaternion eight generates the group
by its action differences; two differences suffice. -/
public theorem eq_mul_cubic_differences_of_equiv {H : Type*} [Group H]
    (model : H ≃* QuaternionGroup 2) (f : MulAut H) (hf : f^3=1) (hne : f≠1)
    (z : H) : ∃ u v, z = (u⁻¹ * f u) * (v⁻¹ * f v) := by
  let e := MulAut.congr model f
  have he : e^3=1 := by dsimp [e]; rw [← map_pow, hf, map_one]
  have hne' : e≠1 := by
    intro h
    apply hne
    exact (MulAut.congr model).injective (h.trans (map_one _).symm)
  obtain ⟨u, v, huv⟩ := eq_mul_cubic_differences_two e he hne' (model z)
  refine ⟨model.symm u, model.symm v, model.injective ?_⟩
  simpa [e, MulAut.congr_apply] using huv

end QuaternionGroup

namespace Subgroup

/-- A normal subgroup containing a cubic actor contains every quaternion factor
on which that actor acts nontrivially. -/
public theorem quaternion_le_normal_of_cubic_actor {G : Type*} [Group G]
    (B N : Subgroup G) [N.Normal] (model : B ≃* QuaternionGroup 2)
    (x : G) (hx : x ∈ N) (f : MulAut B) (hf : f^3=1) (hne : f≠1)
    (hact : ∀ b : B, (f b : G) = x * b * x⁻¹) : B ≤ N := by
  have hd (b : B) : ((b⁻¹ * f b : B) : G) ∈ N := by
    change (b : G)⁻¹ * (f b : G) ∈ N
    rw [hact]
    have hc := (inferInstance : N.Normal).conj_mem x hx (b : G)⁻¹
    simpa only [inv_inv, mul_assoc] using N.mul_mem hc (N.inv_mem hx)
  intro b hb
  obtain ⟨u, v, huv⟩ := QuaternionGroup.eq_mul_cubic_differences_of_equiv
    model f hf hne (⟨b, hb⟩ : B)
  have he := congrArg Subtype.val huv
  change b = ((u⁻¹ * f u : B) : G) * ((v⁻¹ * f v : B) : G) at he
  rw [he]
  exact N.mul_mem (hd u) (hd v)

end Subgroup

