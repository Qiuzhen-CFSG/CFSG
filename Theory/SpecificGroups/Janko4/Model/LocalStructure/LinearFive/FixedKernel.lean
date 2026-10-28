module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Action

/-!
# The common fixed kernel of the four native lifts

The four certified eleven-bit actions have precisely the span of masks
51,73,140,281,515,1041 as common fixed space. The six coordinates are recovered
from bits 5 through 10. A bounded check of 2048 masks certifies the linear
calculation, and the final theorem applies it to actual elements of max1.
-/

public noncomputable section
namespace Janko4.LocalStructure.LinearFive
open Cardinality KernelCount QuotientCount.Image
open Simplicity.Max1Fusion.KernelOrbits
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
  localX localY localKernelSeed basis

private def spanMask (m : ℕ) : ℕ :=
  (List.ofFn (fun j : Fin 6 => if m.testBit (j.val + 5) then kernelMasks j else 0)).foldr Nat.xor 0

set_option maxRecDepth 10000
set_option Elab.async false
private theorem check_blocks {P : ℕ → Prop} {size blocks : ℕ} (hs : 0 < size)
    (h : ∀ b : Fin blocks, ∀ i : Fin size, P (size * b.val + i.val))
    (m : Fin (size * blocks)) : P m.val := by
  have hb : m.val / size < blocks := (Nat.div_lt_iff_lt_mul hs).2
    (by simpa only [Nat.mul_comm] using m.isLt)
  simpa only [Nat.div_add_mod] using
    h ⟨m.val / size, hb⟩ ⟨m.val % size, Nat.mod_lt _ hs⟩
private theorem fixed_block_0 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (0 + m.val) = (0 + m.val)) → spanMask (0 + m.val) = (0 + m.val) := by
  decide +kernel
private theorem fixed_block_1 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (64 + m.val) = (64 + m.val)) → spanMask (64 + m.val) = (64 + m.val) := by
  decide +kernel
private theorem fixed_block_2 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (128 + m.val) = (128 + m.val)) → spanMask (128 + m.val) = (128 + m.val) := by
  decide +kernel
private theorem fixed_block_3 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (192 + m.val) = (192 + m.val)) → spanMask (192 + m.val) = (192 + m.val) := by
  decide +kernel
private theorem fixed_block_4 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (256 + m.val) = (256 + m.val)) → spanMask (256 + m.val) = (256 + m.val) := by
  decide +kernel
private theorem fixed_block_5 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (320 + m.val) = (320 + m.val)) → spanMask (320 + m.val) = (320 + m.val) := by
  decide +kernel
private theorem fixed_block_6 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (384 + m.val) = (384 + m.val)) → spanMask (384 + m.val) = (384 + m.val) := by
  decide +kernel
private theorem fixed_block_7 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (448 + m.val) = (448 + m.val)) → spanMask (448 + m.val) = (448 + m.val) := by
  decide +kernel
private theorem fixed_block_8 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (512 + m.val) = (512 + m.val)) → spanMask (512 + m.val) = (512 + m.val) := by
  decide +kernel
private theorem fixed_block_9 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (576 + m.val) = (576 + m.val)) → spanMask (576 + m.val) = (576 + m.val) := by
  decide +kernel
private theorem fixed_block_10 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (640 + m.val) = (640 + m.val)) → spanMask (640 + m.val) = (640 + m.val) := by
  decide +kernel
private theorem fixed_block_11 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (704 + m.val) = (704 + m.val)) → spanMask (704 + m.val) = (704 + m.val) := by
  decide +kernel
private theorem fixed_block_12 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (768 + m.val) = (768 + m.val)) → spanMask (768 + m.val) = (768 + m.val) := by
  decide +kernel
private theorem fixed_block_13 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (832 + m.val) = (832 + m.val)) → spanMask (832 + m.val) = (832 + m.val) := by
  decide +kernel
private theorem fixed_block_14 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (896 + m.val) = (896 + m.val)) → spanMask (896 + m.val) = (896 + m.val) := by
  decide +kernel
private theorem fixed_block_15 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (960 + m.val) = (960 + m.val)) → spanMask (960 + m.val) = (960 + m.val) := by
  decide +kernel
private theorem fixed_block_16 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (1024 + m.val) = (1024 + m.val)) → spanMask (1024 + m.val) = (1024 + m.val) := by
  decide +kernel
private theorem fixed_block_17 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (1088 + m.val) = (1088 + m.val)) → spanMask (1088 + m.val) = (1088 + m.val) := by
  decide +kernel
private theorem fixed_block_18 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (1152 + m.val) = (1152 + m.val)) → spanMask (1152 + m.val) = (1152 + m.val) := by
  decide +kernel
private theorem fixed_block_19 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (1216 + m.val) = (1216 + m.val)) → spanMask (1216 + m.val) = (1216 + m.val) := by
  decide +kernel
private theorem fixed_block_20 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (1280 + m.val) = (1280 + m.val)) → spanMask (1280 + m.val) = (1280 + m.val) := by
  decide +kernel
private theorem fixed_block_21 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (1344 + m.val) = (1344 + m.val)) → spanMask (1344 + m.val) = (1344 + m.val) := by
  decide +kernel
private theorem fixed_block_22 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (1408 + m.val) = (1408 + m.val)) → spanMask (1408 + m.val) = (1408 + m.val) := by
  decide +kernel
private theorem fixed_block_23 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (1472 + m.val) = (1472 + m.val)) → spanMask (1472 + m.val) = (1472 + m.val) := by
  decide +kernel
private theorem fixed_block_24 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (1536 + m.val) = (1536 + m.val)) → spanMask (1536 + m.val) = (1536 + m.val) := by
  decide +kernel
private theorem fixed_block_25 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (1600 + m.val) = (1600 + m.val)) → spanMask (1600 + m.val) = (1600 + m.val) := by
  decide +kernel
private theorem fixed_block_26 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (1664 + m.val) = (1664 + m.val)) → spanMask (1664 + m.val) = (1664 + m.val) := by
  decide +kernel
private theorem fixed_block_27 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (1728 + m.val) = (1728 + m.val)) → spanMask (1728 + m.val) = (1728 + m.val) := by
  decide +kernel
private theorem fixed_block_28 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (1792 + m.val) = (1792 + m.val)) → spanMask (1792 + m.val) = (1792 + m.val) := by
  decide +kernel
private theorem fixed_block_29 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (1856 + m.val) = (1856 + m.val)) → spanMask (1856 + m.val) = (1856 + m.val) := by
  decide +kernel
private theorem fixed_block_30 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (1920 + m.val) = (1920 + m.val)) → spanMask (1920 + m.val) = (1920 + m.val) := by
  decide +kernel
private theorem fixed_block_31 : ∀ m : Fin 64,
    (∀ i : Fin 4, maskImage (liftKernelMasks i) (1984 + m.val) = (1984 + m.val)) → spanMask (1984 + m.val) = (1984 + m.val) := by
  decide +kernel
private theorem fixed_masks (m : Fin 2048) :
    (∀ i : Fin 4, maskImage (liftKernelMasks i) m.val = m.val) → spanMask m.val = m.val := by
  apply check_blocks (P := fun k => (∀ i : Fin 4, maskImage (liftKernelMasks i) k = k) → spanMask k = k)
    (size := 64) (blocks := 32) (by decide) ?_ m
  intro b
  fin_cases b
  · exact fixed_block_0
  · exact fixed_block_1
  · exact fixed_block_2
  · exact fixed_block_3
  · exact fixed_block_4
  · exact fixed_block_5
  · exact fixed_block_6
  · exact fixed_block_7
  · exact fixed_block_8
  · exact fixed_block_9
  · exact fixed_block_10
  · exact fixed_block_11
  · exact fixed_block_12
  · exact fixed_block_13
  · exact fixed_block_14
  · exact fixed_block_15
  · exact fixed_block_16
  · exact fixed_block_17
  · exact fixed_block_18
  · exact fixed_block_19
  · exact fixed_block_20
  · exact fixed_block_21
  · exact fixed_block_22
  · exact fixed_block_23
  · exact fixed_block_24
  · exact fixed_block_25
  · exact fixed_block_26
  · exact fixed_block_27
  · exact fixed_block_28
  · exact fixed_block_29
  · exact fixed_block_30
  · exact fixed_block_31
private theorem xor_fold_bound (l : List ℕ) (h : ∀ x ∈ l, x < 2048) :
    l.foldr Nat.xor 0 < 2048 := by
  induction l with
  | nil => decide
  | cons a l ih =>
    exact Nat.xor_lt_two_pow (n := 11) (h a (List.mem_cons_self ..))
      (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

private theorem action_bound (i : Fin 4) (m : Fin 2048) :
    maskImage (liftKernelMasks i) m.val < 2048 := by
  have ht : ∀ (i : Fin 4) (j : Fin 11), liftKernelMasks i j < 2048 := by decide +kernel
  apply xor_fold_bound
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
  split_ifs
  · exact ht i j
  · decide

private theorem kernelValue_fold (l : List ℕ) :
    kernelValue (l.foldr Nat.xor 0) = (l.map kernelValue).prod := by
  simpa only [kernelValue, SubmonoidClass.coe_list_prod, List.map_map, Function.comp_def] using
    congrArg (fun z : localKernel matrixA_mul_self matrixB_pow_four => (z : M))
      (maskValue_fold matrixA_mul_self matrixB_pow_four l)

private theorem spanMask_value (m : ℕ) :
    kernelValue (spanMask m) = binaryProduct kernelGenerator (fun j => m.testBit (j.val + 5)) := by
  rw [spanMask, kernelValue_fold]
  simp only [List.map_ofFn, binaryProduct]
  congr 1
  congr 1
  funext j
  dsimp only [Function.comp_apply]
  split_ifs
  · rfl
  · exact kernelValue_zero

/-- The actual common centralizer in the max1 kernel is contained in F. -/
theorem kernel_mem_localF_of_commuting_lifts (z : M)
    (hz : z ∈ localKernel matrixA_mul_self matrixB_pow_four)
    (hc : ∀ i : Fin 4, Commute z (lift i)) : z ∈ localF := by
  obtain ⟨m, hm⟩ := maskValue_surjective matrixA_mul_self matrixB_pow_four ⟨z, hz⟩
  have hm' : kernelValue m.val = z := congrArg Subtype.val hm
  rw [← hm'] at hc ⊢
  have hfix (i : Fin 4) : maskImage (liftKernelMasks i) m.val = m.val := by
    apply kernelValue_injective (action_bound i m) m.isLt
    rw [← lift_conjugates_kernel, mul_assoc, (hc i).eq, inv_mul_cancel_left]
  rw [← fixed_masks m hfix, spanMask_value]
  apply binaryProduct_mem
  intro j
  have h := generator_mem_localF (Fin.castAdd 4 j)
  simpa only [generators, Fin.append_left] using h

end Janko4.LocalStructure.LinearFive
