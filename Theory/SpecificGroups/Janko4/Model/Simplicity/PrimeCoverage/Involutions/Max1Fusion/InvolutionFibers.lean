module
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.OutsideReduction
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.KernelOrbits.Coordinates
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.InvolutionFibers.Data
import Mathlib.Tactic.Group
/-!
# Involutions in the two distinguished local quotient fibers

Write E(m) for the certified eleven-bit kernel coordinates. Equality with the
quotient image of a ∈ {x, (xy)^7} gives w = a E(m). Its square is one exactly
when the right-conjugation action satisfies A(m) xor m = s, where a² = E(s).
Here s = 0 for x and s = 1 for (xy)^7; no splitting of the extension is used.

The finite certificates reduce every solution by a kernel conjugator E(n).
The resulting ten words are precisely `outsideRepresentative`. All
conjugators live in the concrete local subgroup, and the only inputs are the
original matrix square and fourth-power identities.

Source: the literal ATLAS J4G1-max1W1 words in Cardinality.Subgroup and the
certified kernel basis and conjugation tables in Cardinality.LocalOrder.
-/

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
@[expose] public section
namespace Janko4.Simplicity.Max1Fusion.InvolutionFibers
open Cardinality Cardinality.KernelCount Cardinality.QuotientCount.Image KernelOrbits
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
attribute [local irreducible] basis modelGroup matrixA matrixB localKernel
  max1Subgroup localX localY localKernelSeed

private abbrev E (m : ℕ) : max1Subgroup hA hB := maskValue hA hB m

private lemma E_xor (m n : ℕ) : E hA hB (Nat.xor m n) = E hA hB m * E hA hB n :=
  congrArg Subtype.val (maskValue_xor hA hB m n)
private lemma E_zero : E hA hB 0 = 1 := congrArg Subtype.val (maskValue_zero hA hB)
private lemma E_square (m : ℕ) : E hA hB m * E hA hB m = 1 := by
  rw [← E_xor, show Nat.xor m m = 0 from Nat.xor_self m, E_zero]
private lemma E_inv (m : ℕ) : (E hA hB m)⁻¹ = E hA hB m := by
  exact inv_eq_of_mul_eq_one_left (E_square hA hB m)

private lemma E_injective {m n : ℕ} (hm : m < 2048) (hn : n < 2048)
    (h : E hA hB m = E hA hB n) : m = n := by
  have hb := coordinates_injective hA hB (Subtype.ext h : maskValue hA hB m = maskValue hA hB n)
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 11
  · exact congrFun hb ⟨j, hj⟩
  · have hp : 2^11 ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm hp),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hn hp)]

private lemma right_conj_xy_pow (n m : ℕ) :
    ((localX hA hB * localY hA hB)^n)⁻¹ * E hA hB m *
      (localX hA hB * localY hA hB)^n = E hA hB ((xyAction^[n]) m) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    calc
      _ = (localY hA hB)⁻¹ * ((localX hA hB)⁻¹ *
        (((localX hA hB * localY hA hB)^n)⁻¹ * E hA hB m *
          (localX hA hB * localY hA hB)^n) * localX hA hB) * localY hA hB := by group
      _ = E hA hB ((xyAction^[n+1]) m) := by
        rw [ih, right_conj_mask_x, right_conj_mask_y]
        exact congrArg (E hA hB) (Function.iterate_succ_apply' xyAction n m).symm

private lemma right_conj_q (m : ℕ) :
    ((localX hA hB * localY hA hB)^7)⁻¹ * E hA hB m *
      (localX hA hB * localY hA hB)^7 = E hA hB (maskImage qMasks m) := by
  have hb (i : Fin 11) :
      ((localX hA hB * localY hA hB)^7)⁻¹ * basis hA hB i *
        (localX hA hB * localY hA hB)^7 = E hA hB (qMasks i) := by
    rw [← maskValue_basis hA hB i, right_conj_xy_pow, qMasks_basis]
  rw [show E hA hB (maskImage qMasks m) = _ from maskValue_maskImage hA hB qMasks m]
  have h := map_binaryProduct (MulAut.conj ((localX hA hB * localY hA hB)^7)⁻¹).toMonoidHom
    (basis hA hB) (fun i => m.testBit i.val)
  change ((localX hA hB * localY hA hB)^7)⁻¹ * _ *
    (((localX hA hB * localY hA hB)^7)⁻¹)⁻¹ =
      binaryProduct (fun i => ((localX hA hB * localY hA hB)^7)⁻¹ *
        basis hA hB i * (((localX hA hB * localY hA hB)^7)⁻¹)⁻¹)
        (fun i => m.testBit i.val) at h
  simpa only [inv_inv, hb, E, maskValue, coordinates_val] using h

private def base (b : Bool) : max1Subgroup hA hB :=
  if b then (localX hA hB * localY hA hB)^7 else localX hA hB

private lemma right_conj_base (b : Bool) (m : ℕ) :
    (base hA hB b)⁻¹ * E hA hB m * base hA hB b =
      E hA hB (maskImage (actionMasks b) m) := by
  cases b
  · exact right_conj_mask_x hA hB m
  · exact right_conj_q hA hB m

private lemma base_square (b : Bool) :
    base hA hB b * base hA hB b = E hA hB (squareMask b) := by
  cases b
  · exact (localX_mul_self hA hB).trans (E_zero hA hB).symm
  · change ((localX hA hB * localY hA hB)^7) *
      ((localX hA hB * localY hA hB)^7) = E hA hB 1
    rw [← pow_two, ← pow_mul]
    simpa only [localKernelSeed] using (maskValue_one hA hB).symm

private lemma square_equation (b : Bool) (m : Fin 2048)
    (h : (base hA hB b * E hA hB m.val)^2 = 1) :
    Nat.xor (maskImage (actionMasks b) m.val) m.val = squareMask b := by
  have hs : E hA hB (squareMask b) *
      E hA hB (Nat.xor (maskImage (actionMasks b) m.val) m.val) = 1 := by
    rw [E_xor, ← right_conj_base, ← base_square]
    calc
      _ = (base hA hB b * E hA hB m.val)^2 := by simp only [pow_two]; group
      _ = 1 := h
  have he : E hA hB (Nat.xor (maskImage (actionMasks b) m.val) m.val) =
      E hA hB (squareMask b) := by
    calc
      _ = E hA hB (squareMask b) * (E hA hB (squareMask b) *
          E hA hB (Nat.xor (maskImage (actionMasks b) m.val) m.val)) := by
        rw [← mul_assoc, E_square, one_mul]
      _ = _ := by rw [hs, mul_one]
  exact E_injective hA hB (square_bound b m) (by cases b <;> decide) he

private lemma kernel_conjugate (b : Bool) (m n : ℕ) :
    E hA hB n * (base hA hB b * E hA hB m) * (E hA hB n)⁻¹ =
      base hA hB b * E hA hB
        (Nat.xor (Nat.xor (maskImage (actionMasks b) n) m) n) := by
  rw [E_xor, E_xor, ← right_conj_base, E_inv]
  group

private lemma representative_eq (b : Bool) (i : Fin 10) (hi : i.val < 2 ↔ b = false) :
    outsideRepresentative hA hB i = base hA hB b * E hA hB (outsideMask i) := by
  cases b <;> simp_all [outsideRepresentative, base, E, maskValue]

private lemma normal_form (b : Bool) (w : max1Subgroup hA hB)
    (hw : QuotientGroup.mk' (localKernel hA hB) w =
      QuotientGroup.mk' (localKernel hA hB) (base hA hB b)) :
    ∃ m : Fin 2048, w = base hA hB b * E hA hB m.val := by
  have hk : (base hA hB b)⁻¹ * w ∈ localKernel hA hB := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (localKernel hA hB) ((base hA hB b)⁻¹ * w) = 1
    rw [map_mul, map_inv, hw, inv_mul_cancel]
  obtain ⟨m, hm⟩ := maskValue_surjective hA hB ⟨_, hk⟩
  refine ⟨m, ?_⟩
  have he : E hA hB m.val = (base hA hB b)⁻¹ * w := congrArg Subtype.val hm
  rw [he, mul_inv_cancel_left]

private lemma fiber_coverage (b : Bool) (w : max1Subgroup hA hB) (ho : orderOf w = 2)
    (hw : QuotientGroup.mk' (localKernel hA hB) w =
      QuotientGroup.mk' (localKernel hA hB) (base hA hB b)) :
    ∃ (i : Fin 10) (g : max1Subgroup hA hB),
      outsideRepresentative hA hB i = g * w * g⁻¹ := by
  obtain ⟨m, rfl⟩ := normal_form hA hB b w hw
  have hs : (base hA hB b * E hA hB m.val)^2 = 1 := by
    rw [← ho, pow_orderOf_eq_one]
  obtain ⟨hi, he⟩ := reduction b m (square_equation hA hB b m hs)
  refine ⟨(witness b m.val).1, E hA hB (witness b m.val).2, ?_⟩
  rw [kernel_conjugate, he, representative_eq hA hB b _ hi]

end Janko4.Simplicity.Max1Fusion.InvolutionFibers


namespace Janko4.Simplicity.Max1Fusion
open Cardinality
/-- The two quotient fibers contain no additional involution classes under
conjugation by the actual local subgroup. -/
theorem involution_fibers (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (w : max1Subgroup hA hB) (ho : orderOf w = 2)
    (hw : QuotientGroup.mk' (localKernel hA hB) w =
        QuotientGroup.mk' (localKernel hA hB) (localX hA hB) ∨
      QuotientGroup.mk' (localKernel hA hB) w =
        QuotientGroup.mk' (localKernel hA hB) ((localX hA hB * localY hA hB)^7)) :
    ∃ (i : Fin 10) (g : max1Subgroup hA hB),
      outsideRepresentative hA hB i = g * w * g⁻¹ := by
  rcases hw with hx | hq
  · exact InvolutionFibers.fiber_coverage hA hB false w ho hx
  · exact InvolutionFibers.fiber_coverage hA hB true w ho hq
end Janko4.Simplicity.Max1Fusion
