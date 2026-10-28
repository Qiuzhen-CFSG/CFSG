module
public import Theory.SpecificGroups.Triality.ArmsOrbit

/-!
# Transport of intrinsic triality core orbits

Parabolic conjugation preserves orbit sets on Q/Z. Compatible automorphisms
of the whole parabolic and its core preserve their cardinalities, including
those induced by the cubic field extension. Thus the fourteen-element lower
bound applies to the entire short-root quotient orbit and all its central lifts.

Source: Aschbacher--Smith F.4.35, printed p.292. The original core-fusion
application is EightLargeParabolic/FusionOrbit.lean.
-/

public noncomputable section
open Subgroup
namespace Triality.Standard.EvenInvolutionGeometry.ArmsOrbit
open Parabolics
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "Q" => radical P Node.arms
local notation "L" => parabolic P Node.arms

theorem points_action (h : L) (q : Space) : points (action h q)=points q := by
  ext x
  constructor
  · rintro ⟨k,rfl⟩
    refine ⟨k*h,?_⟩
    change action (k*h) q=action k (action h q)
    rw [map_mul,MulAut.mul_apply]
  · rintro ⟨k,rfl⟩
    refine ⟨k*h⁻¹,?_⟩
    change action (k*h⁻¹) (action h q)=action k q
    rw [map_mul,map_inv,MulAut.mul_apply,MulAut.inv_apply,MulEquiv.symm_apply_apply]

theorem points_card_eq_of_compatible (a : MulAut L) (b : MulAut Space)
    (hab : ∀ h : L, ∀ q : Space, b (action h q)=action (a h) (b q)) (q : Space) :
    (points (b q)).ncard=(points q).ncard := by
  have horbit : b '' points q=points (b q) := by
    ext x
    constructor
    · rintro ⟨_,⟨h,rfl⟩,rfl⟩
      exact ⟨a h,(hab h q).symm⟩
    · rintro ⟨h,rfl⟩
      refine ⟨action (a.symm h) q,⟨_,rfl⟩,?_⟩
      rw [hab,a.apply_symm_apply]
  rw [←horbit,Set.ncard_image_of_injective _ b.injective]

theorem point_orbit_card_eq_of_core_compatible (a : MulAut L) (c : MulAut Q)
    (hac : ∀ h : L, ∀ q : Q, c (coreAction h q)=coreAction (a h) (c q)) (q : Q) :
    (points (point (c q))).ncard=(points (point q)).ncard := by
  let b := quotientAut (center Q) c
  have he (q : Q) : b (point q)=point (c q) := quotientAut_apply_mk _ _ _
  have hab (h : L) (u : Space) : b (action h u)=action (a h) (b u) := by
    obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (center Q) u
    change b (action h (point v))=action (a h) (b (point v))
    rw [action_point,he,he,action_point,hac]
  simpa only [he] using points_card_eq_of_compatible a b hab (point q)

theorem short_orbit_point_lower (d : ExtensionField P) (hd : d≠0) (q : Space)
    (hq : q∈points (point ⟨_,short_two_mem d⟩)) : 14≤(points q).ncard := by
  obtain ⟨h,rfl⟩ := hq
  rw [points_action]
  exact short_orbit_lower d hd
end Triality.Standard.EvenInvolutionGeometry.ArmsOrbit
