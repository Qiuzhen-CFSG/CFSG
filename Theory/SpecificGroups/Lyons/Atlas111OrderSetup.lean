module

public import Theory.SpecificGroups.Lyons.Atlas111Group
public import Mathlib.GroupTheory.Index

/-!
# The concrete subgroup for the Lyons order calculation

We evaluate the ATLAS straight-line program `LyG1-max1W1` in the fixed
111-dimensional matrix group. The program specifies two generators for the
subgroup labelled G₂(5) in the ATLAS. Here it defines an actual subgroup, without
assuming that identification. Its cardinality and index are separate obligations.
Lagrange's equality will combine those certificates to count the ambient group.

The literal register computation is followed by proofs of its expanded words,
so the word convention and overwritten registers are explicit.

Source: R. A. Wilson et al., ATLAS of Finite Group Representations,
https://brauer.maths.qmul.ac.uk/Atlas/v3/subgroup/LyG1-max1W1 .
The original program and its hash are in `Atlas111OrderSource/`.
-/

namespace Lyons.OrderCertificate

/-- Execution of the sixteen instructions of the ATLAS subgroup program. -/
@[expose] public def max1Program {G : Type*} [Group G] (a b : G) : G × G :=
  let r3 := a * b
  let r4 := r3 * b
  let r5 := r3 * r4
  let r9 := r5 * b
  let r6 := r3 * r5
  let r7 := r6 * r3
  let r8 := r7 * r7
  let r2 := r7 * r8
  let r3 := r9 ^ 7
  let r4 := r3⁻¹
  let r5 := r3 * a
  let r1 := r5 * r4
  let r8 := r6 ^ 25
  let r7 := r8⁻¹
  let r3 := r7 * r2
  let r2 := r3 * r8
  (r1, r2)

public theorem max1Program_fst {G : Type*} [Group G] (a b : G) :
    (max1Program a b).1 =
      (a * b * a * b ^ 3) ^ 7 * a * ((a * b * a * b ^ 3) ^ 7)⁻¹ := by
  simp only [max1Program, pow_succ, pow_zero, one_mul, mul_assoc]

public theorem max1Program_snd {G : Type*} [Group G] (a b : G) :
    (max1Program a b).2 =
      ((a * b * a * b * a * b ^ 2) ^ 25)⁻¹ *
        (a * b * a * b * a * b ^ 2 * a * b) ^ 3 *
        (a * b * a * b * a * b ^ 2) ^ 25 := by
  simp only [max1Program, pow_succ, pow_zero, one_mul, mul_assoc]

/-- The first output, inside the fixed matrix-generated carrier. -/
@[expose] public def localA : LyonsGroup := (max1Program generatorA generatorB).1

/-- The second output, inside the fixed matrix-generated carrier. -/
@[expose] public def localB : LyonsGroup := (max1Program generatorA generatorB).2

/-- The subgroup whose order and index will be certified. -/
@[expose] public def localSubgroup : Subgroup LyonsGroup :=
  Subgroup.closure {localA, localB}

public theorem localA_mem : localA ∈ localSubgroup :=
  Subgroup.subset_closure (Set.mem_insert _ _)

public theorem localB_mem : localB ∈ localSubgroup :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- The two ambient generators generate the whole concrete carrier. -/
public theorem closure_generators :
    Subgroup.closure ({generatorA, generatorB} : Set LyonsGroup) = ⊤ := by
  have hs : ({generatorA, generatorB} : Set LyonsGroup) =
      atlasSubgroup.subtype ⁻¹' ({atlasA, atlasB} : Set _) := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Subgroup.coe_subtype]
    change (x = generatorA ∨ x = generatorB) ↔
      (x.val = generatorA.val ∨ x.val = generatorB.val)
    exact or_congr Subtype.ext_iff Subtype.ext_iff
  rw [hs]
  exact Subgroup.closure_preimage_eq_top _

/-- Lagrange's equality for this specified subgroup. -/
public theorem card_eq_local_card_mul_index :
    Nat.card LyonsGroup = Nat.card localSubgroup * localSubgroup.index :=
  localSubgroup.card_mul_index.symm

end Lyons.OrderCertificate
