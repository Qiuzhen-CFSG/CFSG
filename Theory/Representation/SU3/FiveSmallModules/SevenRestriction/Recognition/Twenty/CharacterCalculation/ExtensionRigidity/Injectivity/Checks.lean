module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.ExtensionRigidity.Injectivity.Data

/-!
# Kernel checks for the averaged Bruhat matrix certificate

The selected 400 rows are checked against the sums of the literal nine
coefficient pairs, and their candidate left inverse is checked by XOR scans.
Arithmetic interprets these scans over any characteristic-two field.

A ten-row probe took 9.78 seconds for equation agreement and 1.72 seconds
for inverse rows (2.75 GB peak RSS including imports). Declaration checking
is serialized here to bound memory on the shared machine; the ordinary Lean
thread default is retained. No native computation is used.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity.Injectivity.Certificate
open Data

def flat (r c : Fin 20) : Fin 400 := ⟨20*r.val+c.val, by omega⟩

private theorem rows_0 : ∀ c : Fin 20,
    let j := flat 0 c
    let p := position j
    equationData[j.val]! = systemRow p.1 p.2.1 p.2.2 := by decide +kernel

private theorem rows_1 : ∀ c : Fin 20,
    let j := flat 1 c
    let p := position j
    equationData[j.val]! = systemRow p.1 p.2.1 p.2.2 := by decide +kernel

private theorem rows_2 : ∀ c : Fin 20,
    let j := flat 2 c
    let p := position j
    equationData[j.val]! = systemRow p.1 p.2.1 p.2.2 := by decide +kernel

private theorem rows_3 : ∀ c : Fin 20,
    let j := flat 3 c
    let p := position j
    equationData[j.val]! = systemRow p.1 p.2.1 p.2.2 := by decide +kernel

private theorem rows_4 : ∀ c : Fin 20,
    let j := flat 4 c
    let p := position j
    equationData[j.val]! = systemRow p.1 p.2.1 p.2.2 := by decide +kernel

private theorem rows_5 : ∀ c : Fin 20,
    let j := flat 5 c
    let p := position j
    equationData[j.val]! = systemRow p.1 p.2.1 p.2.2 := by decide +kernel

private theorem rows_6 : ∀ c : Fin 20,
    let j := flat 6 c
    let p := position j
    equationData[j.val]! = systemRow p.1 p.2.1 p.2.2 := by decide +kernel

private theorem rows_7 : ∀ c : Fin 20,
    let j := flat 7 c
    let p := position j
    equationData[j.val]! = systemRow p.1 p.2.1 p.2.2 := by decide +kernel

private theorem rows_8 : ∀ c : Fin 20,
    let j := flat 8 c
    let p := position j
    equationData[j.val]! = systemRow p.1 p.2.1 p.2.2 := by decide +kernel

private theorem rows_9 : ∀ c : Fin 20,
    let j := flat 9 c
    let p := position j
    equationData[j.val]! = systemRow p.1 p.2.1 p.2.2 := by decide +kernel

private theorem rows_10 : ∀ c : Fin 20,
    let j := flat 10 c
    let p := position j
    equationData[j.val]! = systemRow p.1 p.2.1 p.2.2 := by decide +kernel

private theorem rows_11 : ∀ c : Fin 20,
    let j := flat 11 c
    let p := position j
    equationData[j.val]! = systemRow p.1 p.2.1 p.2.2 := by decide +kernel

private theorem rows_12 : ∀ c : Fin 20,
    let j := flat 12 c
    let p := position j
    equationData[j.val]! = systemRow p.1 p.2.1 p.2.2 := by decide +kernel

private theorem rows_13 : ∀ c : Fin 20,
    let j := flat 13 c
    let p := position j
    equationData[j.val]! = systemRow p.1 p.2.1 p.2.2 := by decide +kernel

private theorem rows_14 : ∀ c : Fin 20,
    let j := flat 14 c
    let p := position j
    equationData[j.val]! = systemRow p.1 p.2.1 p.2.2 := by decide +kernel

private theorem rows_15 : ∀ c : Fin 20,
    let j := flat 15 c
    let p := position j
    equationData[j.val]! = systemRow p.1 p.2.1 p.2.2 := by decide +kernel

private theorem rows_16 : ∀ c : Fin 20,
    let j := flat 16 c
    let p := position j
    equationData[j.val]! = systemRow p.1 p.2.1 p.2.2 := by decide +kernel

private theorem rows_17 : ∀ c : Fin 20,
    let j := flat 17 c
    let p := position j
    equationData[j.val]! = systemRow p.1 p.2.1 p.2.2 := by decide +kernel

private theorem rows_18 : ∀ c : Fin 20,
    let j := flat 18 c
    let p := position j
    equationData[j.val]! = systemRow p.1 p.2.1 p.2.2 := by decide +kernel

private theorem rows_19 : ∀ c : Fin 20,
    let j := flat 19 c
    let p := position j
    equationData[j.val]! = systemRow p.1 p.2.1 p.2.2 := by decide +kernel

private theorem inverse_0 : ∀ c : Fin 20,
    let j := flat 0 c
    PackedBinaryRows.listProduct inverseData[j.val]! 0 equationData.toList = 2 ^ j.val := by
  decide +kernel

private theorem inverse_1 : ∀ c : Fin 20,
    let j := flat 1 c
    PackedBinaryRows.listProduct inverseData[j.val]! 0 equationData.toList = 2 ^ j.val := by
  decide +kernel

private theorem inverse_2 : ∀ c : Fin 20,
    let j := flat 2 c
    PackedBinaryRows.listProduct inverseData[j.val]! 0 equationData.toList = 2 ^ j.val := by
  decide +kernel

private theorem inverse_3 : ∀ c : Fin 20,
    let j := flat 3 c
    PackedBinaryRows.listProduct inverseData[j.val]! 0 equationData.toList = 2 ^ j.val := by
  decide +kernel

private theorem inverse_4 : ∀ c : Fin 20,
    let j := flat 4 c
    PackedBinaryRows.listProduct inverseData[j.val]! 0 equationData.toList = 2 ^ j.val := by
  decide +kernel

private theorem inverse_5 : ∀ c : Fin 20,
    let j := flat 5 c
    PackedBinaryRows.listProduct inverseData[j.val]! 0 equationData.toList = 2 ^ j.val := by
  decide +kernel

private theorem inverse_6 : ∀ c : Fin 20,
    let j := flat 6 c
    PackedBinaryRows.listProduct inverseData[j.val]! 0 equationData.toList = 2 ^ j.val := by
  decide +kernel

private theorem inverse_7 : ∀ c : Fin 20,
    let j := flat 7 c
    PackedBinaryRows.listProduct inverseData[j.val]! 0 equationData.toList = 2 ^ j.val := by
  decide +kernel

private theorem inverse_8 : ∀ c : Fin 20,
    let j := flat 8 c
    PackedBinaryRows.listProduct inverseData[j.val]! 0 equationData.toList = 2 ^ j.val := by
  decide +kernel

private theorem inverse_9 : ∀ c : Fin 20,
    let j := flat 9 c
    PackedBinaryRows.listProduct inverseData[j.val]! 0 equationData.toList = 2 ^ j.val := by
  decide +kernel

private theorem inverse_10 : ∀ c : Fin 20,
    let j := flat 10 c
    PackedBinaryRows.listProduct inverseData[j.val]! 0 equationData.toList = 2 ^ j.val := by
  decide +kernel

private theorem inverse_11 : ∀ c : Fin 20,
    let j := flat 11 c
    PackedBinaryRows.listProduct inverseData[j.val]! 0 equationData.toList = 2 ^ j.val := by
  decide +kernel

private theorem inverse_12 : ∀ c : Fin 20,
    let j := flat 12 c
    PackedBinaryRows.listProduct inverseData[j.val]! 0 equationData.toList = 2 ^ j.val := by
  decide +kernel

private theorem inverse_13 : ∀ c : Fin 20,
    let j := flat 13 c
    PackedBinaryRows.listProduct inverseData[j.val]! 0 equationData.toList = 2 ^ j.val := by
  decide +kernel

private theorem inverse_14 : ∀ c : Fin 20,
    let j := flat 14 c
    PackedBinaryRows.listProduct inverseData[j.val]! 0 equationData.toList = 2 ^ j.val := by
  decide +kernel

private theorem inverse_15 : ∀ c : Fin 20,
    let j := flat 15 c
    PackedBinaryRows.listProduct inverseData[j.val]! 0 equationData.toList = 2 ^ j.val := by
  decide +kernel

private theorem inverse_16 : ∀ c : Fin 20,
    let j := flat 16 c
    PackedBinaryRows.listProduct inverseData[j.val]! 0 equationData.toList = 2 ^ j.val := by
  decide +kernel

private theorem inverse_17 : ∀ c : Fin 20,
    let j := flat 17 c
    PackedBinaryRows.listProduct inverseData[j.val]! 0 equationData.toList = 2 ^ j.val := by
  decide +kernel

private theorem inverse_18 : ∀ c : Fin 20,
    let j := flat 18 c
    PackedBinaryRows.listProduct inverseData[j.val]! 0 equationData.toList = 2 ^ j.val := by
  decide +kernel

private theorem inverse_19 : ∀ c : Fin 20,
    let j := flat 19 c
    PackedBinaryRows.listProduct inverseData[j.val]! 0 equationData.toList = 2 ^ j.val := by
  decide +kernel

private theorem rows_by_pair (r c : Fin 20) :
    let j := flat r c
    let p := position j
    equationData[j.val]! = systemRow p.1 p.2.1 p.2.2 := by
  fin_cases r
  · exact rows_0 c
  · exact rows_1 c
  · exact rows_2 c
  · exact rows_3 c
  · exact rows_4 c
  · exact rows_5 c
  · exact rows_6 c
  · exact rows_7 c
  · exact rows_8 c
  · exact rows_9 c
  · exact rows_10 c
  · exact rows_11 c
  · exact rows_12 c
  · exact rows_13 c
  · exact rows_14 c
  · exact rows_15 c
  · exact rows_16 c
  · exact rows_17 c
  · exact rows_18 c
  · exact rows_19 c

private theorem inverse_by_pair (r c : Fin 20) :
    let j := flat r c
    PackedBinaryRows.listProduct inverseData[j.val]! 0 equationData.toList = 2 ^ j.val := by
  fin_cases r
  · exact inverse_0 c
  · exact inverse_1 c
  · exact inverse_2 c
  · exact inverse_3 c
  · exact inverse_4 c
  · exact inverse_5 c
  · exact inverse_6 c
  · exact inverse_7 c
  · exact inverse_8 c
  · exact inverse_9 c
  · exact inverse_10 c
  · exact inverse_11 c
  · exact inverse_12 c
  · exact inverse_13 c
  · exact inverse_14 c
  · exact inverse_15 c
  · exact inverse_16 c
  · exact inverse_17 c
  · exact inverse_18 c
  · exact inverse_19 c

/-- Every retained equation is the stated sum of tensor coefficients. -/
theorem selected_equations (i : Fin 400) :
    let p := position i
    equationData[i.val]! = systemRow p.1 p.2.1 p.2.2 := by
  let r : Fin 20 := ⟨i.val / 20, by omega⟩
  let c : Fin 20 := ⟨i.val % 20, by omega⟩
  have he : flat r c = i := by apply Fin.ext; dsimp [flat, r, c]; omega
  simpa only [he] using rows_by_pair r c

/-- The candidate inverse recovers each of the 400 unknown entries. -/
theorem inverse_checked (i : Fin 400) :
    PackedBinaryRows.listProduct inverseData[i.val]! 0 equationData.toList = 2 ^ i.val := by
  let r : Fin 20 := ⟨i.val / 20, by omega⟩
  let c : Fin 20 := ⟨i.val % 20, by omega⟩
  have he : flat r c = i := by apply Fin.ext; dsimp [flat, r, c]; omega
  simpa only [he] using inverse_by_pair r c

theorem equationData_size : equationData.size = 400 := by decide +kernel

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity.Injectivity.Certificate
