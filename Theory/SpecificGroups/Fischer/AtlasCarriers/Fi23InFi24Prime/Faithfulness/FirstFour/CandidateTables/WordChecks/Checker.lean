module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.CandidateTables.WordChecks.Contracts
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.InverseCheck

/-!
# Strict finite checks for the shared-word contracts

Evaluating the input and block indices before lookup avoids repeating their
reductions. The two case-split lemmas prove equality with the original packed
lookup. The soundness theorems recover the exact Fin-valued contracts; padding
uses reduction modulo 306936. Exhaustive certificates can be produced for the
three tests independently and combined only in the final word assembly.

Source: the exact lists in `WordEvaluation`, retained ATLAS F24G1-p306936B0,
and GLS3 Table 5.3v. No computation outside Lean supplies a proof premise.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.CandidateTables.WordChecks
open Certificate Certificate.Ambient

def strictBlocks (t : PackedBlocks) : Nat → Nat
  | 0 => t.get 0
  | i + 1 => t.get (i + 1)

def table (t : PackedBlocks) : Nat → Nat
  | 0 => lookup (strictBlocks t) 19 0 % 306936
  | i + 1 => lookup (strictBlocks t) 19 (i + 1) % 306936

theorem strictBlocks_eq (t : PackedBlocks) (i : Nat) :
    strictBlocks t i = t.get i := by
  cases i <;> rfl

theorem table_eq (t : PackedBlocks) (i : Nat) :
    table t i = lookup t.get 19 i % 306936 := by
  cases i <;> simp only [table, lookup, strictBlocks_eq]

def dictionaryTest (i : Nat) : Bool :=
  let x := i % 306936
  (table d04MapData x == table aBlocksTree (table bInvBlocksTree (x))) &&
  (table d05MapData x == table aBlocksTree (table bBlocksTree (x))) &&
  (table d06MapData x == table d04MapData (table d04MapData (x))) &&
  (table d07MapData x == table d05MapData (table d05MapData (x))) &&
  (table d08MapData x == table d04MapData (table d05MapData (x))) &&
  (table d09MapData x == table d04MapData (table d07MapData (x))) &&
  (table d10MapData x == table d08MapData (table d06MapData (x))) &&
  (table d11MapData x == table d07MapData (table d06MapData (x))) &&
  (table d12MapData x == table d05MapData (table d06MapData (x))) &&
  (table d13MapData x == table d10MapData (table d07MapData (x))) &&
  (table d14MapData x == table d06MapData (table d09MapData (x)))

theorem dictionaryTest_sound (h : ∀ i : Fin 306936, dictionaryTest i.val = true) :
    DictionaryChecks := by
  have checks (i : Fin 306936) := h i
  simp only [dictionaryTest, Nat.mod_eq_of_lt (Fin.isLt _), Bool.and_eq_true,
    beq_iff_eq, table_eq] at checks
  constructor
  · intro x
    exact Fin.ext ((checks x).1.1.1.1.1.1.1.1.1.1)
  · intro x
    exact Fin.ext ((checks x).1.1.1.1.1.1.1.1.1.2)
  · intro x
    exact Fin.ext ((checks x).1.1.1.1.1.1.1.1.2)
  · intro x
    exact Fin.ext ((checks x).1.1.1.1.1.1.1.2)
  · intro x
    exact Fin.ext ((checks x).1.1.1.1.1.1.2)
  · intro x
    exact Fin.ext ((checks x).1.1.1.1.1.2)
  · intro x
    exact Fin.ext ((checks x).1.1.1.1.2)
  · intro x
    exact Fin.ext ((checks x).1.1.1.2)
  · intro x
    exact Fin.ext ((checks x).1.1.2)
  · intro x
    exact Fin.ext ((checks x).1.2)
  · intro x
    exact Fin.ext ((checks x).2)

def outputTestA (i : Nat) : Bool :=
  let x := i % 306936
  (table vMapData x == table d14MapData (table d05MapData (table d09MapData (table d09MapData (table d11MapData (table d12MapData (table d10MapData (table d09MapData (table d10MapData (table d13MapData (table d08MapData (table d04MapData (table aBlocksTree (x)))))))))))))) &&
  (table rMapData x == table d12MapData (table d13MapData (table d07MapData (table d05MapData (table d09MapData (table d07MapData (table d11MapData (table d07MapData (table d13MapData (table d12MapData (table d11MapData (table d08MapData (table aBlocksTree (x)))))))))))))) &&
  (table wMapData x == table d10MapData (table d09MapData (table d11MapData (table d14MapData (table d09MapData (table d14MapData (table d11MapData (table d14MapData (table d06MapData (table d07MapData (table d08MapData (table d04MapData (x)))))))))))))

theorem outputTestA_sound (h : ∀ i : Fin 306936, outputTestA i.val = true) :
    OutputChecksA := by
  have checks (i : Fin 306936) := h i
  simp only [outputTestA, Nat.mod_eq_of_lt (Fin.isLt _), Bool.and_eq_true,
    beq_iff_eq, table_eq] at checks
  constructor
  · intro x
    exact Fin.ext ((checks x).1.1)
  · intro x
    exact Fin.ext ((checks x).1.2)
  · intro x
    exact Fin.ext ((checks x).2)

def outputTestB (i : Nat) : Bool :=
  let x := i % 306936
  (table uMapData x == table bInvBlocksTree (table d10MapData (table d09MapData (table d07MapData (table d10MapData (table d08MapData (table d09MapData (table d12MapData (table d06MapData (table d06MapData (table d13MapData (table aBlocksTree (x))))))))))))) &&
  (table sMapData x == table bBlocksTree (table d11MapData (table d11MapData (table d10MapData (table d10MapData (table d12MapData (table d09MapData (table d07MapData (table d05MapData (table d09MapData (table d09MapData (table d08MapData (table d04MapData (x))))))))))))))

theorem outputTestB_sound (h : ∀ i : Fin 306936, outputTestB i.val = true) :
    OutputChecksB := by
  have checks (i : Fin 306936) := h i
  simp only [outputTestB, Nat.mod_eq_of_lt (Fin.isLt _), Bool.and_eq_true,
    beq_iff_eq, table_eq] at checks
  constructor
  · intro x
    exact Fin.ext ((checks x).1)
  · intro x
    exact Fin.ext ((checks x).2)

end Sporadic.Fischer.Fi24Prime.Fi23Lift.CandidateTables.WordChecks
