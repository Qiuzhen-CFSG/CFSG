module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Index

/-!
# Lifting involution squares through a dihedral quotient

The preimage of the rotations in a dihedral quotient of order eight has
index two. Its outside-kernel involutions map to the central half-turn.

More generally, let a surjection have a nonidentity central involution in
its image that is a square. If the involutions in its fiber form one orbit
under the kernel, and the kernel elements centralizing one of them have
square one, then that involution is a square upstairs. Correct a lift of a
quotient square root by kernel conjugacy so it centralizes the involution.
Its square differs from that involution by a fixed kernel element, hence
is itself an involution. A second kernel conjugation gives the desired root.

This is the square-root argument in Janko–Thompson, Math. Z. 113 (1970),
§4, case (c), printed p.392. The quaternion action establishing the fiber
hypotheses is independent of this group-theoretic lifting step.
-/

open Subgroup

namespace MonoidHom

/-- A central square in a quotient lifts to a square when the involution
fiber is transitive under the kernel and the fixed kernel has exponent two. -/
public theorem square_root_of_involution_fiber
    {T Q : Type*} [Group T] [Group Q] (f : T →* Q)
    (hf : Function.Surjective f) (u : T) (hu : orderOf u = 2)
    (hcentral : f u ∈ center Q) (hne : f u ≠ 1) (a : Q) (ha : a ^ 2 = f u)
    (hfixed : ∀ w : T, f w = 1 → Commute w u → w ^ 2 = 1)
    (hfiber : ∀ v : T, orderOf v = 2 → f v = f u →
      ∃ p : f.ker, (p : T) * u * (p : T)⁻¹ = v) :
    ∃ r : T, r ^ 2 = u := by
  obtain ⟨s, hs⟩ := hf a
  have hus : orderOf ((MulAut.conj s) u) = 2 :=
    ((MulAut.conj s).orderOf_eq u).trans hu
  have hfus : f ((MulAut.conj s) u) = f u := by
    change f (s * u * s⁻¹) = f u
    rw [map_mul, map_mul, map_inv, mem_center_iff.mp hcentral (f s)]
    simp
  obtain ⟨p, hp⟩ := hfiber ((MulAut.conj s) u) hus hfus
  let k : T := (p : T)⁻¹ * s
  have hk : Commute k u := by
    change (p : T)⁻¹ * s * u = u * ((p : T)⁻¹ * s)
    have hh := congrArg (fun x : T => (p : T)⁻¹ * x * s) hp
    simpa only [MulAut.conj_apply, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one] using hh.symm
  have hfk : f k = a := by
    change f ((p : T)⁻¹ * s) = a
    rw [map_mul, map_inv, show f (p : T) = 1 from p.property, inv_one, one_mul, hs]
  have hfksq : f (k ^ 2) = f u := by rw [map_pow, hfk, ha]
  have hdiff : f (k ^ 2 * u⁻¹) = 1 := by rw [map_mul, map_inv, hfksq, mul_inv_cancel]
  have hdiffcomm : Commute (k ^ 2 * u⁻¹) u :=
    (hk.pow_left 2).mul_left (Commute.refl u).inv_left
  have hdiffsq := hfixed (k ^ 2 * u⁻¹) hdiff hdiffcomm
  have hu2 : u ^ 2 = 1 := by simpa only [hu] using pow_orderOf_eq_one u
  have hksq2 : (k ^ 2) ^ 2 = 1 := by
    rw [((hk.pow_left 2).inv_right).mul_pow, inv_pow, hu2, inv_one, mul_one] at hdiffsq
    exact hdiffsq
  have hk2 : orderOf (k ^ 2) = 2 := orderOf_eq_prime hksq2 (by
    intro h
    apply hne
    rw [← hfksq, h, map_one])
  obtain ⟨q, hq⟩ := hfiber (k ^ 2) hk2 hfksq
  refine ⟨(MulAut.conj (q : T)).symm k, ?_⟩
  apply (MulAut.conj (q : T)).injective
  rw [map_pow, MulEquiv.apply_symm_apply]
  exact hq.symm

end MonoidHom

namespace DihedralGroup

/-- The preimage of the cyclic subgroup of rotations in a dihedral quotient. -/
@[expose] public def rotationPreimage {T : Type*} [Group T] (f : T →* DihedralGroup 4) : Subgroup T :=
  (zpowers (r 1 : DihedralGroup 4)).comap f

/-- The rotation preimage of a surjection has index two. -/
public theorem rotationPreimage_index {T : Type*} [Group T]
    (f : T →* DihedralGroup 4) (hf : Function.Surjective f) :
    (rotationPreimage f).index = 2 := by
  rw [rotationPreimage, index_comap_of_surjective _ hf]
  have h := (zpowers (r 1 : DihedralGroup 4)).card_mul_index
  rw [Nat.card_zpowers, orderOf_r_one, nat_card] at h
  omega

/-- The kernel lies in the rotation preimage. -/
public theorem ker_le_rotationPreimage {T : Type*} [Group T]
    (f : T →* DihedralGroup 4) : f.ker ≤ rotationPreimage f :=
  (zpowers (r 1 : DihedralGroup 4)).ker_le_comap f

/-- A rotation involution outside the kernel maps to the half-turn. -/
public theorem image_eq_r_two_of_rotation_involution {T : Type*} [Group T]
    (f : T →* DihedralGroup 4) (u : T) (hu : orderOf u = 2)
    (hrot : u ∈ rotationPreimage f) (hne : f u ≠ 1) : f u = r 2 := by
  have hu2 : (f u) ^ 2 = 1 := by
    rw [← map_pow, show u ^ 2 = 1 by simpa only [hu] using pow_orderOf_eq_one u, map_one]
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hrot
  rw [r_one_zpow] at hn
  have hi : (n : ZMod 4) = 0 ∨ (n : ZMod 4) = 2 := by
    rw [← hn] at hu2
    have hz : ∀ i : ZMod 4, (r i : DihedralGroup 4) ^ 2 = 1 → i = 0 ∨ i = 2 := by decide
    exact hz _ hu2
  rcases hi with hi | hi
  · exact (hne (by rw [← hn, hi, r_zero])).elim
  · rw [← hn, hi]

/-- The half-turn is central in the dihedral group of order eight. -/
public theorem r_two_mem_center : (r 2 : DihedralGroup 4) ∈ center (DihedralGroup 4) := by
  apply mem_center_iff.mpr
  decide

/-- The unique involution fiber above the nonidentity rotation square lifts
to squares when its fixed kernel elements have exponent two. -/
public theorem square_root_of_rotation_involution {T : Type*} [Group T]
    (f : T →* DihedralGroup 4) (hf : Function.Surjective f)
    (u : T) (hu : orderOf u = 2) (hrot : u ∈ rotationPreimage f)
    (hne : f u ≠ 1)
    (hfixed : ∀ w : T, f w = 1 → Commute w u → w ^ 2 = 1)
    (hfiber : ∀ v : T, orderOf v = 2 → f v = f u →
      ∃ p : f.ker, (p : T) * u * (p : T)⁻¹ = v) :
    ∃ r : T, r ^ 2 = u := by
  have himage := image_eq_r_two_of_rotation_involution f u hu hrot hne
  exact f.square_root_of_involution_fiber hf u hu
    (himage ▸ r_two_mem_center) hne (r 1)
    (by rw [himage, r_one_pow]; rfl) hfixed hfiber

end DihedralGroup
