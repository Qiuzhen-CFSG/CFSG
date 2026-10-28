module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.AmbientConditions
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.RestrictionRigidity
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity

/-!
# Assembly of the full seed-centralizer algebra kernel bound

The two independent finite rigidity theorems first match the restriction of
an algebra-valued centralizer element with a known local-kernel element,
then classify the centralizer elements fixing K pointwise as one or the seed.
Dividing by the matched element proves membership in the actual order-2048
ambient local kernel, and hence the cardinality bound.

The original conditional reductions are retained. The final theorems discharge
both rigidity premises using the imported finite proofs. Only membership of
the literal restriction in `Coordinates.concreteAlgebra` remains as input;
the intrinsic action's kernel-to-algebra bridge belongs to the ambient-order
assembly.

Source: `KernelBound/source/README.md` and the finite witnesses described in
the source workspace's `Scratch/J4FleetGuidance/SeedCentralizer/README.md`.
-/

public section

namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound
open Coordinates Cardinality

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernelSeed

theorem mem_ambientKernel_of_restriction_and_pointwise
    (hRestriction : ∀ c : SeedCentralizer, restriction c ∈ concreteAlgebra →
      ∃ e : ambientKernel, restriction (kernelCentralizerInclusion e) = restriction c)
    (hPointwise : ∀ c : SeedCentralizer, restriction c = 1 →
      (c : Model) = 1 ∨ (c : Model) = (localKernelSeed matrixA_mul_self matrixB_pow_four : Model))
    (c : SeedCentralizer) (hc : restriction c ∈ concreteAlgebra) :
    (c : Model) ∈ ambientKernel := by
  obtain ⟨e, he⟩ := hRestriction c hc
  let d : SeedCentralizer := (kernelCentralizerInclusion e)⁻¹ * c
  have hd : restriction d = 1 := by
    change restriction ((kernelCentralizerInclusion e)⁻¹ * c) = 1
    rw [map_mul, ← he, ← map_mul, inv_mul_cancel, map_one]
  have hdmem : (d : Model) ∈ ambientKernel := by
    rcases hPointwise d hd with h | h
    · rw [h]; exact ambientKernel.one_mem
    · rw [h]; exact seed_mem_ambientKernel
  have hprod := ambientKernel.mul_mem e.property hdmem
  simpa only [d, Subgroup.coe_mul, Subgroup.coe_inv,
    show (kernelCentralizerInclusion e : Model) = (e : Model) from rfl,
    mul_inv_cancel_left] using hprod

theorem algebraCentralizer_card_le_of_restriction_and_pointwise
    (hRestriction : ∀ c : SeedCentralizer, restriction c ∈ concreteAlgebra →
      ∃ e : ambientKernel, restriction (kernelCentralizerInclusion e) = restriction c)
    (hPointwise : ∀ c : SeedCentralizer, restriction c = 1 →
      (c : Model) = 1 ∨ (c : Model) = (localKernelSeed matrixA_mul_self matrixB_pow_four : Model)) :
    Nat.card {c : SeedCentralizer // restriction c ∈ concreteAlgebra} ≤ 2048 := by
  let f : {c : SeedCentralizer // restriction c ∈ concreteAlgebra} → ambientKernel :=
    fun c => ⟨c.val, mem_ambientKernel_of_restriction_and_pointwise hRestriction hPointwise c.val c.property⟩
  have hf : Function.Injective f := by
    intro c d h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ambientKernel => (z : Model)) h
  simpa only [ambientKernel_card] using Nat.card_le_card_of_injective f hf

/-- Every full seed-centralizer element whose literal restriction belongs to
the concrete algebra lies in the actual order-2048 ambient local kernel. -/
theorem mem_ambientKernel_of_restriction_mem
    (c : SeedCentralizer) (hc : restriction c ∈ concreteAlgebra) :
    (c : Model) ∈ ambientKernel :=
  mem_ambientKernel_of_restriction_and_pointwise
    exists_ambientKernel_same_restriction eq_one_or_seed_of_restriction_eq_one c hc

/-- There are at most 2048 full seed-centralizer matrices with restriction in
the concrete algebra. Both restriction and pointwise rigidity are discharged. -/
theorem algebraCentralizer_card_le :
    Nat.card {c : SeedCentralizer // restriction c ∈ concreteAlgebra} ≤ 2048 :=
  algebraCentralizer_card_le_of_restriction_and_pointwise
    exists_ambientKernel_same_restriction eq_one_or_seed_of_restriction_eq_one

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound
