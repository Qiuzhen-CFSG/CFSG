module

public import Theory.SpecificGroups.Thompson.Model.Basic
public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates

/-!
# The ATLAS word subgroup for counting Thompson's matrix group

The straight-line program `ThG1-max1W1` specifies two words in the certified
matrix generators. We define their actual subgroup, without assuming the
ATLAS identification as `³D₄(2):3`, its order, or its index. The first word is
a conjugate of the source involution. The second is transcribed using the
program's intermediate registers, including the overwrite of register 8.

Source: https://brauer.maths.qmul.ac.uk/Atlas/v3/subgroup/ThG1-max1W1 .
The original program and transcription notes are preserved in `Order/source/`.
-/

namespace Thompson.OrderCertificate

/-- First output of `ThG1-max1W1`: `(ab)⁻⁸ a (ab)⁸`. -/
@[expose] public def localA : Model :=
  ((generatorA * generatorB) ^ 8)⁻¹ * generatorA *
    (generatorA * generatorB) ^ 8

/-- Register 8 immediately before the fifth power in `ThG1-max1W1`.
The two versions of register 8 are distinguished to preserve the overwrite. -/
@[expose] public def localBBase : Model :=
  let r3 := generatorA * generatorB
  let r4 := r3 * generatorB
  let r5 := r3 * r4
  let r6 := r3 * r5
  let r7 := r6 * r3
  let r8 := r7 * r4
  let r9 := r3 * r8
  r7 * r9

/-- Second output of `ThG1-max1W1`. -/
@[expose] public def localB : Model := localBBase ^ 5

/-- The concrete word-generated subgroup, with no identification assumed. -/
@[expose] public def localSubgroup : Subgroup Model :=
  Subgroup.closure {localA, localB}

public theorem localA_mem : localA ∈ localSubgroup :=
  Subgroup.subset_closure (Set.mem_insert _ _)

public theorem localB_mem : localB ∈ localSubgroup :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- Conjugation preserves the already certified square relation. -/
public theorem localA_sq : localA ^ 2 = 1 := by
  have ha : generatorA * generatorA = 1 := by
    simpa only [pow_two] using generatorA_sq
  simp [localA, pow_two, mul_assoc, ← mul_assoc generatorA generatorA, ha]

/-- The first local generator is nonidentity, since the source generators
do not commute. -/
public theorem localA_ne_one : localA ≠ 1 := by
  intro h
  have ha : generatorA = 1 := by
    have hh := congrArg
      (fun x : Model => (generatorA * generatorB) ^ 8 * x *
        ((generatorA * generatorB) ^ 8)⁻¹) h
    simpa [localA, mul_assoc] using hh
  exact generator_mul_ne (by simp [ha])

end Thompson.OrderCertificate
