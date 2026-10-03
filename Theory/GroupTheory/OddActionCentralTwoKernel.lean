module
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Group.Action.Basic

/-!
# Points fixed by odd actions through a central two-kernel

Let a finite group A of odd order act by automorphisms on G. Suppose a
central two-subgroup N is fixed pointwise. If all action discrepancies
(a • g)g⁻¹ of one chosen element g lie in N, then every element of A fixes
g. The whole-group statement follows as a wrapper when this holds for all
g. The actual given action is retained, and neither G nor N is assumed
finite. No invariant-subgroup assumption is needed for the pointwise theorem.

For each g, its discrepancy is a homomorphism A → N: pointwise fixation
gives the multiplication rule in reverse order, and centrality commutes
the two factors. Each image element has order dividing both |A| and a
power of two. Coprimality forces it to be the identity.

This is the central-kernel action transfer used in ABG II.3 Proposition3,
article p27 (PDF page28), when the odd complement fixes the projected
Sylow subgroup and its central kernel.
-/

namespace MulDistribMulAction

/-- A single point whose discrepancies lie in the fixed central two-kernel
is fixed by the entire odd-order acting group. -/
public theorem fixed_of_odd_of_central_two_discrepancy
    {A G : Type*} [Group A] [Finite A] [Group G] [MulDistribMulAction A G]
    (hA : Odd (Nat.card A)) (N : Subgroup G) (hN : N ≤ Subgroup.center G)
    (hNtwo : IsPGroup 2 N) (hfix : ∀ a : A, ∀ x ∈ N, a • x = x)
    (g : G) (hquot : ∀ a : A, (a • g) * g⁻¹ ∈ N) :
    ∀ a : A, a • g = g := by
  intro a
  let d : A →* N := {
    toFun := fun b => ⟨(b • g) * g⁻¹, hquot b⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := by
      intro b c
      apply Subtype.ext
      change ((b * c) • g) * g⁻¹ = ((b • g) * g⁻¹) * ((c • g) * g⁻¹)
      calc
        ((b * c) • g) * g⁻¹ = (b • (((c • g) * g⁻¹) * g)) * g⁻¹ := by
          rw [inv_mul_cancel_right, mul_smul]
        _ = ((c • g) * g⁻¹) * ((b • g) * g⁻¹) := by
          rw [smul_mul', hfix b _ (hquot c), mul_assoc]
        _ = ((b • g) * g⁻¹) * ((c • g) * g⁻¹) :=
          Subgroup.mem_center_iff.mp (hN (hquot b)) _ }
  obtain ⟨k, hk⟩ := hNtwo.exists_orderOf_dvd_pow (d a)
  have hda : orderOf (d a) ∣ Nat.card A :=
    (orderOf_map_dvd d a).trans (orderOf_dvd_natCard a)
  have horder : orderOf (d a) = 1 :=
    Nat.eq_one_of_dvd_coprimes (hA.coprime_two_right.pow_right k) hda hk
  have he : d a = 1 := orderOf_eq_one_iff.mp horder
  exact mul_inv_eq_one.mp (congrArg Subtype.val he)

/-- Compatibility wrapper for triviality of the action on every point. -/
public theorem trivial_of_odd_of_central_two_kernel
    {A G : Type*} [Group A] [Finite A] [Group G] [MulDistribMulAction A G]
    (hA : Odd (Nat.card A)) (N : Subgroup G) (hN : N ≤ Subgroup.center G)
    (hNtwo : IsPGroup 2 N) (hfix : ∀ a : A, ∀ x ∈ N, a • x = x)
    (hquot : ∀ a : A, ∀ g : G, (a • g) * g⁻¹ ∈ N) :
    ∀ a : A, ∀ g : G, a • g = g := by
  intro a g
  exact fixed_of_odd_of_central_two_discrepancy hA N hN hNtwo hfix g
    (fun b => hquot b g) a

end MulDistribMulAction
