module

public import Theory.GroupAction.InvolutionDisplacementCard
public import Theory.GroupAction.FourthPowerFixed
public import Mathlib.GroupTheory.Index

/-!
# Fixed points of actions trivial on an index-two subgroup

If an index-two subgroup of the actors fixes a finite elementary binary
group pointwise, its order is at most the square of the common fixed
subgroup order. A representative of the other coset acts with square one;
its fixed points are precisely the common fixed points. Apply the
involution fixed/displacement count and the containment of displacement
in the fixed subgroup.

This is the elementary action count used in Parrott (1972), p.676,
in the lower bound for the center of the chosen centralizer.
-/

open Subgroup

/-- An action trivial on an index-two subgroup has at least square-root
many fixed points on every finite elementary binary module. -/
public theorem card_le_fixed_card_sq_of_index_two_kernel
    {Q V : Type*} [Group Q] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction Q V]
    (N : Subgroup Q) (hN : N.index = 2)
    (hfix : ∀ n ∈ N, ∀ v : V, n • v = v) :
    Nat.card V ≤ Nat.card (FixedPoints.subgroup Q V) ^ 2 := by
  obtain ⟨a, _, ha⟩ := index_eq_two_iff_exists_notMem_and.mp hN
  let f : Q →* MulAut V := MulDistribMulAction.toMulAut Q V
  have hsquare : (f a) ^ 2 = 1 := by
    rw [← map_pow]
    ext v
    exact hfix _ (N.sq_mem_of_index_two hN a) v
  have hfixed : FixedPoints.subgroup (zpowers (f a)) V = FixedPoints.subgroup Q V := by
    ext v
    rw [MulAut.mem_fixed_zpowers_iff]
    constructor
    · intro hv b
      rcases ha b with hb | hb
      · have hh := hfix _ hb v
        rw [mul_smul, show a • v = v from hv] at hh
        exact hh
      · exact hfix b hb v
    · intro hv
      exact hv a
  obtain ⟨hc, hle⟩ := MulAut.involution_fixed_displacement_card_data (f a) hsquare
  have hd := card_le_of_le hle
  rw [hfixed] at hc hd
  rw [hc, pow_two]
  exact Nat.mul_le_mul_left _ hd
