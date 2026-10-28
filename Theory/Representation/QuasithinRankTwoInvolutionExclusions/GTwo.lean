module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.GTwo.LongRoot
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.GTwo.InvolutionClasses

/-!
# The binary G₂ moved-plane exclusion

In the full split-octonion group G₂(2), the bound on orders of products of
conjugate involutions forces the long-root class. Conjugating the group and
acting by the same element on its six-dimensional trace-zero quotient gives
an equivalence of representations. The explicit long-root three-cycle thus
makes the stabilizer of the moved plane transitive on its nonzero vectors.

The final adapter transports this calculation through actual group and module
isomorphisms. It contradicts the nontransitivity in 6.2.16(6), completing the
G.11.2(6) branch. The product-order bound is retained as an explicit input from
the parent symplectic argument; neither conjugacy nor transitivity is assumed.

Source: Aschbacher–Smith, proof of 6.2.19, printed p.691 (PDF p.708),
case G.11.2(6), printed p.364 (PDF p.375), and 6.2.16(4),(6), printed p.689
(PDF p.706). The original conjugacy-conditional interface remains available.
-/

@[expose] public section

open Atlas.G2 Atlas.G2.Natural

namespace Representation.RankTwo.GTwo

private def actionEquiv (h : G) : V ≃ₗ[K] V where
  toLinearMap := action K h
  invFun := action K h⁻¹
  left_inv x := by
    change action K h⁻¹ (action K h x) = x
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]
  right_inv x := by
    change action K h (action K h⁻¹ x) = x
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]

private theorem actionEquiv_intertwines (h g : G) (x : V) :
    actionEquiv h (action K g x) = action K (MulAut.conj h g) (actionEquiv h x) := by
  change action K h (action K g x) = action K (h * g * h⁻¹) (action K h x)
  simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]

/-- Actual conjugacy transports the proved long-root stabilizer action. -/
theorem stabilizerTransitive_of_isConj (v : G) (hv : IsConj v (rootA 1)) :
    StabilizerTransitive (action K) (movedSpace (action K) v) := by
  obtain ⟨h, hh⟩ := isConj_iff.mp hv
  apply stabilizerTransitive_transport (action K) (action K) (MulAut.conj h)
    (actionEquiv h) (actionEquiv_intertwines h) v
  simpa only [MulAut.conj_apply, hh] using stabilizerTransitive_rootA

/-- The long-root class calculation and its explicit centralizing three-cycle
give transitivity for every eligible rank-two involution of the full G₂(2). -/
theorem stabilizerTransitive_of_rank_two (v : G) (hv : orderOf v = 2)
    (hrank : Module.finrank K (movedSpace (action K) v) = 2)
    (hprod : ∀ h : G, orderOf (v * (h⁻¹ * v * h)) ≤ 4) :
    StabilizerTransitive (action K) (movedSpace (action K) v) :=
  stabilizerTransitive_of_isConj v (isConj_rootA_of_rank_two v hv hrank hprod)

section Transport
variable {H W : Type*} [Group H] [AddCommGroup W] [Module K W]

/-- The moved-plane normalizer calculation for an action identified equivariantly
with the actual full G₂(2) natural module, using the source convention
`v^h = h⁻¹ * v * h`. -/
theorem stabilizerTransitive_of_equivariant_model
    (ρ : Representation K H W) (e : H ≃* G) (f : W ≃ₗ[K] V)
    (hf : ∀ g z, f (ρ g z) = action K (e g) (f z))
    (v : H) (hv : orderOf v = 2)
    (hrank : Module.finrank K (movedSpace ρ v) = 2)
    (hprod : ∀ h : H, orderOf (v * (h⁻¹ * v * h)) ≤ 4) :
    StabilizerTransitive ρ (movedSpace ρ v) := by
  apply stabilizerTransitive_transport ρ (action K) e f hf v
  apply stabilizerTransitive_of_rank_two (e v) ((e.orderOf_eq v).trans hv)
  · exact (finrank_movedSpace_transport ρ (action K) e f hf v).symm.trans hrank
  · intro h
    calc
      orderOf (e v * (h⁻¹ * e v * h)) =
          orderOf (e (v * ((e.symm h)⁻¹ * v * e.symm h))) := by
        simp only [map_mul, map_inv, e.apply_symm_apply]
      _ = orderOf (v * ((e.symm h)⁻¹ * v * e.symm h)) := e.orderOf_eq _
      _ ≤ 4 := hprod _

/-- Case G.11.2(6) contradicts the nontransitivity of 6.2.16(6).
The source identification of the natural action supplies `e`, `f`, and `hf`;
the parent symplectic argument supplies the conjugate-product order bound. -/
theorem exclusion_of_equivariant_model
    (ρ : Representation K H W) (e : H ≃* G) (f : W ≃ₗ[K] V)
    (hf : ∀ g z, f (ρ g z) = action K (e g) (f z))
    (v : H) (hv : orderOf v = 2)
    (hrank : Module.finrank K (movedSpace ρ v) = 2)
    (hprod : ∀ h : H, orderOf (v * (h⁻¹ * v * h)) ≤ 4)
    (hnontransitive : ¬ StabilizerTransitive ρ (movedSpace ρ v)) : False :=
  hnontransitive (stabilizerTransitive_of_equivariant_model ρ e f hf v hv hrank hprod)

end Transport

end Representation.RankTwo.GTwo
