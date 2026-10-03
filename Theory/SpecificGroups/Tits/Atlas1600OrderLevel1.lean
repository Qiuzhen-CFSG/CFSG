module

public import Theory.SpecificGroups.Tits.Atlas1600OrderLevel1Data
import Mathlib.Tactic.FinCases

/-!
# The 351-point stabilizer-chain step in the Atlas degree-1600 model

The representatives have distinct images of base point 1. Each signed generator
maps each representative to another representative times a word in the level-2
generators. Checking these identities and using the word-subgroup bijection gives
`Nat.card H1 = 351 * Nat.card H2`.

The pointwise identities are checked by the kernel in 27 batches of 13
representatives. Sequential elaboration bounds the memory used by these checks.
The witnesses originate from the Atlas permutations in
`refs/original/n-group-global/atlas-tits-p1600-{a,b}.g`.
-/

namespace Tits.Atlas1600OrderCertificate
open Theory.GroupTheory
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000
set_option Elab.async false

private def batchRep (b : Fin 27) (r : Fin 13) : Fin 351 :=
  ⟨13 * b.val + r.val, by omega⟩

private def stepBatch (b : Fin 27) : Prop :=
  ∀ (i : Fin 6) (r : Fin 13),
    L1Gen i * L1Rep (batchRep b r) =
      L1Rep (L1Act i (batchRep b r)) * evalWord L2Gen (L1Factor i (batchRep b r))

private theorem stepBatch0 : stepBatch 0 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch1 : stepBatch 1 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch2 : stepBatch 2 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch3 : stepBatch 3 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch4 : stepBatch 4 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch5 : stepBatch 5 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch6 : stepBatch 6 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch7 : stepBatch 7 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch8 : stepBatch 8 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch9 : stepBatch 9 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch10 : stepBatch 10 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch11 : stepBatch 11 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch12 : stepBatch 12 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch13 : stepBatch 13 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch14 : stepBatch 14 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch15 : stepBatch 15 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch16 : stepBatch 16 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch17 : stepBatch 17 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch18 : stepBatch 18 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch19 : stepBatch 19 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch20 : stepBatch 20 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch21 : stepBatch 21 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch22 : stepBatch 22 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch23 : stepBatch 23 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch24 : stepBatch 24 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch25 : stepBatch 25 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatch26 : stepBatch 26 := by
  intro i r
  apply Equiv.ext
  revert i r
  apply allFin₃
  decide +kernel

private theorem stepBatches (b : Fin 27) : stepBatch b := by
  fin_cases b
  · exact stepBatch0
  · exact stepBatch1
  · exact stepBatch2
  · exact stepBatch3
  · exact stepBatch4
  · exact stepBatch5
  · exact stepBatch6
  · exact stepBatch7
  · exact stepBatch8
  · exact stepBatch9
  · exact stepBatch10
  · exact stepBatch11
  · exact stepBatch12
  · exact stepBatch13
  · exact stepBatch14
  · exact stepBatch15
  · exact stepBatch16
  · exact stepBatch17
  · exact stepBatch18
  · exact stepBatch19
  · exact stepBatch20
  · exact stepBatch21
  · exact stepBatch22
  · exact stepBatch23
  · exact stepBatch24
  · exact stepBatch25
  · exact stepBatch26

public theorem L1Step (i : Fin 6) (r : Fin 351) :
    L1Gen i * L1Rep r = L1Rep (L1Act i r) * evalWord L2Gen (L1Factor i r) := by
  let b : Fin 27 := ⟨r.val / 13, by omega⟩
  let s : Fin 13 := ⟨r.val % 13, by omega⟩
  have hrs : batchRep b s = r := by
    apply Fin.ext
    dsimp [batchRep, b, s]
    omega
  simpa only [hrs] using stepBatches b i s

public theorem H1_card_step : Nat.card H1 = 351 * Nat.card H2 := by
  exact wordSubgroup_card_eq_mul_next
    L1Gen L1Inv L1Inv_spec L2Gen L2Inv L2Inv_spec
    L1Rep L1Act L1Factor (1 : Fin 1600) L1Point (0 : Fin 351)
    L1Rep_mem H2_le L1Rep_base L1Rep_point L1Point_injective H2_fix L1Step

end Tits.Atlas1600OrderCertificate
