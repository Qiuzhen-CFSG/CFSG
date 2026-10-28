module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.TensorCoordinates
public import Theory.Representation.BinaryPermutation.ThreeTensorDisplacement
public import Mathlib.Tactic

/-!
# The actual binary S₃ factor in eight-dimensional tensor products

The factor is the augmentation core on three letters. Its transposition and
three-cycle act in the existing tensor coordinates by the displayed mixed
and cubic operators. Every involution with a nontrivial S₃ component moves
four dimensions. A rank-two actor therefore belongs to the other factor;
the marked three-cycle acts fixed-point freely on its moved plane.

Source: Aschbacher–Smith, G.11.2(9), printed p.364 (PDF p.375), and the
case-(9) calculation in 6.2.19, printed p.691 (PDF p.708).
The order of the factors here is W tensor the natural S₃ plane.
-/

@[expose] public section

open scoped TensorProduct
namespace Representation.RankTwo.TensorModels
abbrev S3 := Equiv.Perm (Fin 3)
abbrev Plane := BinaryPermutation.core (Fin 3)
/-- A marked three-cycle with coordinate action (x,y) ↦ (y,x+y). -/
def cubicElement : S3 := Equiv.swap 0 1 * Equiv.swap 0 2
lemma cubicElement_order : orderOf cubicElement = 3 := by
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel
lemma involution_conjugate_swap (s : S3) (hs : s * s = 1) (hne : s ≠ 1) :
    ∃ q : S3, s = q * Equiv.swap 0 1 * q⁻¹ := by
  revert s
  decide +kernel

variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]

lemma coordinates_swap (ρ : Representation (ZMod 2) H W) (h : H)
    (z : W ⊗[ZMod 2] Plane) :
    BinaryPermutation.ThreeTensor.pairEquiv
      (BinaryPermutation.ThreeTensor.action ρ (h, Equiv.swap 0 1) z) =
      TensorCoordinates.mixed (ρ h) (BinaryPermutation.ThreeTensor.pairEquiv z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul w n => simp [TensorCoordinates.mixed, BinaryPermutation.coreRepresentation,
      BinaryPermutation.representation]
  | add z w hz hw => simp only [map_add, hz, hw]

lemma coordinates_cubic (ρ : Representation (ZMod 2) H W)
    (z : W ⊗[ZMod 2] Plane) :
    BinaryPermutation.ThreeTensor.pairEquiv
      (BinaryPermutation.ThreeTensor.action ρ (1, cubicElement) z) =
      TensorCoordinates.cubic (BinaryPermutation.ThreeTensor.pairEquiv z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul w n =>
    have hn : n.val 2 = n.val 0 + n.val 1 := by
      have he := n.property
      rw [BinaryPermutation.mem_core, Fin.sum_univ_three] at he
      simpa only [CharTwo.neg_eq] using (eq_neg_of_add_eq_zero_left he).symm
    simp only [BinaryPermutation.ThreeTensor.action_tmul,
      BinaryPermutation.ThreeTensor.pairEquiv_tmul, map_one, Module.End.one_apply]
    change (n.val 1 • w, n.val 2 • w) = (n.val 1 • w, n.val 0 • w + n.val 1 • w)
    rw [hn, add_smul]
  | add z w hz hw => simp only [map_add, hz, hw]

lemma cubic_fixed_free (ρ : Representation (ZMod 2) H W)
    (z : W ⊗[ZMod 2] Plane)
    (hz : BinaryPermutation.ThreeTensor.action ρ (1, cubicElement) z = z) : z = 0 := by
  apply BinaryPermutation.ThreeTensor.pairEquiv.injective
  rw [map_zero]
  exact TensorCoordinates.cubic_fixed_free _ ((coordinates_cubic ρ z).symm.trans
    (congrArg BinaryPermutation.ThreeTensor.pairEquiv hz))

lemma finrank_tensor [FiniteDimensional (ZMod 2) W]
    (hd : Module.finrank (ZMod 2) W = 4) :
    Module.finrank (ZMod 2) (W ⊗[ZMod 2] Plane) = 8 := by
  rw [Module.finrank_tensorProduct, BinaryPermutation.finrank_core, hd]
  rfl

lemma first_factor_of_rank_two [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (hd : Module.finrank (ZMod 2) W = 4)
    (g : H × S3)
    (hr : Module.finrank (ZMod 2) (movedSpace (BinaryPermutation.ThreeTensor.action ρ) g) = 2) :
    g.2 = 1 := by
  by_contra h
  have he := BinaryPermutation.ThreeTensor.dimension_le_displacement ρ g h
  change Module.finrank (ZMod 2) W ≤
    Module.finrank (ZMod 2) (movedSpace (BinaryPermutation.ThreeTensor.action ρ) g) at he
  rw [hd, hr] at he
  omega

lemma involution_rank_le_half {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] (a : Module.End (ZMod 2) U) (ha : a * a = 1) :
    2 * Module.finrank (ZMod 2) (LinearMap.range (a - 1)) ≤ Module.finrank (ZMod 2) U := by
  have hle : LinearMap.range (a - 1) ≤ LinearMap.ker (a - 1) := by
    rintro _ ⟨v, rfl⟩
    change a (a v - v) - (a v - v) = 0
    rw [map_sub, show a (a v) = v from LinearMap.congr_fun ha v]
    have hn (x : U) : -x = x := by
      apply neg_eq_of_add_eq_zero_left
      have h := @two_smul (ZMod 2) U _ _ _ x
      rw [show (2 : ZMod 2) = 0 by decide, zero_smul] at h
      exact h.symm
    simp only [sub_eq_add_neg, hn]
    have hzero (x : U) : x + x = 0 := by
      calc
        x + x = -x + x := congrArg (· + x) (hn x).symm
        _ = 0 := neg_add_cancel x
    calc
      v + a v + (a v + v) = (v + v) + (a v + a v) := by abel
      _ = 0 := by rw [hzero, hzero, zero_add]
  have hr := (a - 1).finrank_range_add_finrank_ker
  have hb := Submodule.finrank_mono hle
  omega

lemma finrank_mixed_involution [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (hd : Module.finrank (ZMod 2) W = 4)
    (g : H × S3) (hg : g * g = 1) (hs : g.2 ≠ 1) :
    Module.finrank (ZMod 2) (movedSpace (BinaryPermutation.ThreeTensor.action ρ) g) = 4 := by
  have hlo := BinaryPermutation.ThreeTensor.dimension_le_displacement ρ g hs
  have hup := involution_rank_le_half (BinaryPermutation.ThreeTensor.action ρ g)
    (by rw [← map_mul, hg, map_one])
  rw [finrank_tensor hd] at hup
  rw [hd] at hlo
  change 4 ≤ Module.finrank (ZMod 2) (movedSpace (BinaryPermutation.ThreeTensor.action ρ) g) at hlo
  change 2 * Module.finrank (ZMod 2) (movedSpace (BinaryPermutation.ThreeTensor.action ρ) g) ≤ 8 at hup
  omega

lemma stabilizerTransitive_first [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (h : H)
    (hr : Module.finrank (ZMod 2)
      (movedSpace (BinaryPermutation.ThreeTensor.action ρ) (h, 1)) = 2) :
    StabilizerTransitive (BinaryPermutation.ThreeTensor.action ρ)
      (movedSpace (BinaryPermutation.ThreeTensor.action ρ) (h, 1)) := by
  apply stabilizerTransitive_of_order_three _ _ (1, cubicElement) hr
  · change (1, cubicElement) * (h, 1) = (h, 1) * (1, cubicElement)
    simp
  · apply Prod.ext
    · simp
    · change cubicElement ^ 3 = 1
      simpa only [cubicElement_order] using pow_orderOf_eq_one cubicElement
  · intro z _ hz
    exact cubic_fixed_free ρ z hz
end Representation.RankTwo.TensorModels
