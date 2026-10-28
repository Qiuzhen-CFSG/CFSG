module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.OverlapExtensions.CentralExtensions.Coordinates

/-!
# Right Cayley edges of the first outer M₁₂ endpoint

The checked coordinate signatures identify each tabulated right product with
the actual product by one of the four generators. These are the exact edges
used to construct the two parity characters. The short point maps and word
tables come from `Coordinates`, with its source and ATLAS attribution.
-/
@[expose] public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.OverlapExtensions
namespace Endpoint
set_option maxRecDepth 100000
-- Check finite blocks sequentially to bound temporary reduction memory.
set_option Elab.async false

private def stepCorrect (i : Fin 384) (j : Fin 4) : Prop :=
  let w := Data.endpointWords i
  (evaluatePoint w (generatorMap j 0), evaluatePoint w (generatorMap j 1),
    evaluatePoint w (generatorMap j 2)) = indexSignature (Data.endpointStep i j)
private instance (i : Fin 384) (j : Fin 4) : Decidable (stepCorrect i j) :=
  inferInstanceAs (Decidable ((evaluatePoint (Data.endpointWords i) (generatorMap j 0),
    evaluatePoint (Data.endpointWords i) (generatorMap j 1),
    evaluatePoint (Data.endpointWords i) (generatorMap j 2)) =
    indexSignature (Data.endpointStep i j)))

private theorem step_0 : ∀ i : Fin 16,
    ∀ j : Fin 4, stepCorrect ⟨0 + i.val, by omega⟩ j := by decide +kernel

private theorem step_1 : ∀ i : Fin 16,
    ∀ j : Fin 4, stepCorrect ⟨16 + i.val, by omega⟩ j := by decide +kernel

private theorem step_2 : ∀ i : Fin 16,
    ∀ j : Fin 4, stepCorrect ⟨32 + i.val, by omega⟩ j := by decide +kernel

private theorem step_3 : ∀ i : Fin 16,
    ∀ j : Fin 4, stepCorrect ⟨48 + i.val, by omega⟩ j := by decide +kernel

private theorem step_4 : ∀ i : Fin 16,
    ∀ j : Fin 4, stepCorrect ⟨64 + i.val, by omega⟩ j := by decide +kernel

private theorem step_5 : ∀ i : Fin 16,
    ∀ j : Fin 4, stepCorrect ⟨80 + i.val, by omega⟩ j := by decide +kernel

private theorem step_6 : ∀ i : Fin 16,
    ∀ j : Fin 4, stepCorrect ⟨96 + i.val, by omega⟩ j := by decide +kernel

private theorem step_7 : ∀ i : Fin 16,
    ∀ j : Fin 4, stepCorrect ⟨112 + i.val, by omega⟩ j := by decide +kernel

private theorem step_8 : ∀ i : Fin 16,
    ∀ j : Fin 4, stepCorrect ⟨128 + i.val, by omega⟩ j := by decide +kernel

private theorem step_9 : ∀ i : Fin 16,
    ∀ j : Fin 4, stepCorrect ⟨144 + i.val, by omega⟩ j := by decide +kernel

private theorem step_10 : ∀ i : Fin 16,
    ∀ j : Fin 4, stepCorrect ⟨160 + i.val, by omega⟩ j := by decide +kernel

private theorem step_11 : ∀ i : Fin 16,
    ∀ j : Fin 4, stepCorrect ⟨176 + i.val, by omega⟩ j := by decide +kernel

private theorem step_12 : ∀ i : Fin 16,
    ∀ j : Fin 4, stepCorrect ⟨192 + i.val, by omega⟩ j := by decide +kernel

private theorem step_13 : ∀ i : Fin 16,
    ∀ j : Fin 4, stepCorrect ⟨208 + i.val, by omega⟩ j := by decide +kernel

private theorem step_14 : ∀ i : Fin 16,
    ∀ j : Fin 4, stepCorrect ⟨224 + i.val, by omega⟩ j := by decide +kernel

private theorem step_15 : ∀ i : Fin 16,
    ∀ j : Fin 4, stepCorrect ⟨240 + i.val, by omega⟩ j := by decide +kernel

private theorem step_16 : ∀ i : Fin 16,
    ∀ j : Fin 4, stepCorrect ⟨256 + i.val, by omega⟩ j := by decide +kernel

private theorem step_17 : ∀ i : Fin 16,
    ∀ j : Fin 4, stepCorrect ⟨272 + i.val, by omega⟩ j := by decide +kernel

private theorem step_18 : ∀ i : Fin 16,
    ∀ j : Fin 4, stepCorrect ⟨288 + i.val, by omega⟩ j := by decide +kernel

private theorem step_19 : ∀ i : Fin 16,
    ∀ j : Fin 4, stepCorrect ⟨304 + i.val, by omega⟩ j := by decide +kernel

private theorem step_20 : ∀ i : Fin 16,
    ∀ j : Fin 4, stepCorrect ⟨320 + i.val, by omega⟩ j := by decide +kernel

private theorem step_21 : ∀ i : Fin 16,
    ∀ j : Fin 4, stepCorrect ⟨336 + i.val, by omega⟩ j := by decide +kernel

private theorem step_22 : ∀ i : Fin 16,
    ∀ j : Fin 4, stepCorrect ⟨352 + i.val, by omega⟩ j := by decide +kernel

private theorem step_23 : ∀ i : Fin 16,
    ∀ j : Fin 4, stepCorrect ⟨368 + i.val, by omega⟩ j := by decide +kernel

private theorem step_block (b : Fin 24) : ∀ i : Fin 16,
    ∀ j : Fin 4, stepCorrect ⟨16 * b.val + i.val, by omega⟩ j := by
  fin_cases b
  · exact step_0
  · exact step_1
  · exact step_2
  · exact step_3
  · exact step_4
  · exact step_5
  · exact step_6
  · exact step_7
  · exact step_8
  · exact step_9
  · exact step_10
  · exact step_11
  · exact step_12
  · exact step_13
  · exact step_14
  · exact step_15
  · exact step_16
  · exact step_17
  · exact step_18
  · exact step_19
  · exact step_20
  · exact step_21
  · exact step_22
  · exact step_23

private theorem step_check (i : Fin 384) (j : Fin 4) : stepCorrect i j := by
  have h := step_block ⟨i.val / 16, by omega⟩ ⟨i.val % 16, by omega⟩ j
  have e : (⟨16 * (i.val / 16) + i.val % 16, by omega⟩ : Fin 384) = i := by
    apply Fin.ext
    change 16 * (i.val / 16) + i.val % 16 = i.val
    omega
  exact e ▸ h

theorem element_step (i : Fin 384) (j : Fin 4) :
    element (Data.endpointStep i j) = element i * generator j := by
  apply signature_injective
  rw [signature_element]
  unfold signature
  simp only [Subgroup.coe_mul, Equiv.Perm.coe_mul]
  rw [element_val, generator_val]
  simp only [Function.comp_apply, evaluatePoint_spec, generatorMap_spec]
  exact (step_check i j).symm

end Endpoint
end Sporadic.Mathieu.M12ExceptionalExtension.OverlapExtensions
