module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.Defs
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.FiberData
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.KernelOrbits.Coordinates
import Mathlib.Tactic.Group

/-!
# Bounds for the seed-type lifts of quotient involutions

Every lift over x or (xy)^7 is uniquely a fixed lift times an eleven-bit
kernel element. Its square is one only if its mask solves the certified
affine equation. The latter fiber has 128 solutions. In the former fiber,
32 of the 64 solutions are conjugate to the first ambient representative;
class separation excludes them, leaving at most 32 seed-type elements.

The normal-form and conjugation calculations adapt the proofs in
`Max1Fusion.InvolutionFibers` to the counting interfaces. Source: the literal
ATLAS J4G1-max1W1 words and the kernel certificates cited in that module.
Neither quotient centralization nor splitting of the extension is assumed.
-/

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true
public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound
open Cardinality Cardinality.KernelCount Cardinality.QuotientCount.Image
open Simplicity.Max1Fusion Simplicity.Max1Fusion.KernelOrbits
open Simplicity.Max1Fusion.InvolutionFibers
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


private noncomputable def fiberMask (b : Bool) (w : BaseFiber hA hB b) : Fin 2048 :=
  (normal_form hA hB b w.val w.property.2).choose

private theorem fiberMask_spec (b : Bool) (w : BaseFiber hA hB b) :
    w.val = base hA hB b * E hA hB (fiberMask hA hB b w).val :=
  (normal_form hA hB b w.val w.property.2).choose_spec

private theorem fiberMask_injective (b : Bool) : Function.Injective (fiberMask hA hB b) := by
  intro w v h
  apply Subtype.ext
  rw [fiberMask_spec hA hB b w, fiberMask_spec hA hB b v, h]

private theorem fiberMask_solution (b : Bool) (w : BaseFiber hA hB b) :
    fiberMask hA hB b w ∈ affineSolutions b := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, square_equation hA hB b _ ?_⟩
  rw [← fiberMask_spec hA hB b w, ← colored_order hA hB w.val w.property.1,
    pow_orderOf_eq_one]

/-- At most 128 seed-type lifts occur over the second quotient representative.
This counts the full quotient fiber, before restricting to the centralizer. -/
theorem baseFiber_true_card_le : Nat.card (BaseFiber hA hB true) ≤ 128 := by
  classical
  let f : BaseFiber hA hB true → {m // m ∈ affineSolutions true} :=
    fun w => ⟨fiberMask hA hB true w, fiberMask_solution hA hB true w⟩
  have hf : Function.Injective f := by
    intro w v h
    exact fiberMask_injective hA hB true (congrArg Subtype.val h)
  have h := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, affineSolutions_true_card] using h

private theorem fiberMask_nonFirst
    (hn : ¬ IsConj (Simplicity.a hA) (localKernelSeed hA hB : Model))
    (w : BaseFiber hA hB false) : fiberMask hA hB false w ∈ nonFirstSolutions := by
  classical
  refine Finset.mem_filter.mpr ⟨fiberMask_solution hA hB false w, ?_⟩
  intro hz
  let m := fiberMask hA hB false w
  have hs := (Finset.mem_filter.mp (fiberMask_solution hA hB false w)).2
  obtain ⟨hi, he⟩ := reduction false m hs
  have hc : IsConj w.val (outsideRepresentative hA hB 0) := by
    apply isConj_iff.mpr
    refine ⟨E hA hB (witness false m.val).2, ?_⟩
    rw [fiberMask_spec hA hB false w, kernel_conjugate, he, hz]
    exact (representative_eq hA hB false 0 (by decide)).symm
  have hx : outsideRepresentative hA hB 0 = localX hA hB := by
    rw [representative_eq hA hB false 0 (by decide)]
    change localX hA hB * E hA hB 0 = localX hA hB
    rw [E_zero, mul_one]
  rw [hx] at hc
  obtain ⟨g, hg⟩ := localX_fuses_first hA hB
  have ha : IsConj (localX hA hB : Model) (Simplicity.a hA) :=
    isConj_iff.mpr ⟨g, hg.symm⟩
  exact hn (ha.symm.trans
    (((max1Subgroup hA hB).subtype.map_isConj hc).symm.trans w.property.1.symm))

/-- Class separation leaves at most 32 seed-type lifts over the first
quotient representative. All lifts are counted, including those outside the
local seed centralizer. -/
theorem baseFiber_false_card_le
    (hn : ¬ IsConj (Simplicity.a hA) (localKernelSeed hA hB : Model)) :
    Nat.card (BaseFiber hA hB false) ≤ 32 := by
  classical
  let f : BaseFiber hA hB false → {m // m ∈ nonFirstSolutions} :=
    fun w => ⟨fiberMask hA hB false w, fiberMask_nonFirst hA hB hn w⟩
  have hf : Function.Injective f := by
    intro w v h
    exact fiberMask_injective hA hB false (congrArg Subtype.val h)
  have h := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, nonFirstSolutions_card] using h

end Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound
