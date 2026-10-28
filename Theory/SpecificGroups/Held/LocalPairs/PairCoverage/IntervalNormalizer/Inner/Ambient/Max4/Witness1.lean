module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.LocalWords

/-! Kernel-checked conjugation and order identities for the literal max4
local witness 1. See `LocalWords` for source attribution and word conventions. -/

namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.Witness1

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem check0 : ∀ x : Fin 4,
    representation (localWitness 1 * schreierGenerator (largeRow 1) 0 * (localWitness 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (evalSchreierWord (largeRow 1) (conjugateWord 1 0))
      ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem check1 : ∀ x : Fin 4,
    representation (localWitness 1 * schreierGenerator (largeRow 1) 1 * (localWitness 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (evalSchreierWord (largeRow 1) (conjugateWord 1 1))
      ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem check2 : ∀ x : Fin 4,
    representation (localWitness 1 * schreierGenerator (largeRow 1) 2 * (localWitness 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (evalSchreierWord (largeRow 1) (conjugateWord 1 2))
      ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem check3 : ∀ x : Fin 4,
    representation (localWitness 1 * schreierGenerator (largeRow 1) 3 * (localWitness 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (evalSchreierWord (largeRow 1) (conjugateWord 1 3))
      ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem check4 : ∀ x : Fin 4,
    representation (localWitness 1 * schreierGenerator (largeRow 1) 4 * (localWitness 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (evalSchreierWord (largeRow 1) (conjugateWord 1 4))
      ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem check5 : ∀ x : Fin 4,
    representation (localWitness 1 * schreierGenerator (largeRow 1) 5 * (localWitness 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (evalSchreierWord (largeRow 1) (conjugateWord 1 5))
      ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem check6 : ∀ x : Fin 4,
    representation (localWitness 1 * schreierGenerator (largeRow 1) 6 * (localWitness 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (evalSchreierWord (largeRow 1) (conjugateWord 1 6))
      ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem check7 : ∀ x : Fin 4,
    representation (localWitness 1 * schreierGenerator (largeRow 1) 7 * (localWitness 1)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (evalSchreierWord (largeRow 1) (conjugateWord 1 7))
      ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
public theorem conjugate_eq (r : Fin 8) :
    localWitness 1 * schreierGenerator (largeRow 1) r * (localWitness 1)⁻¹ =
      evalSchreierWord (largeRow 1) (conjugateWord 1 r) := by
  apply Held.eq_of_four_point_images
  fin_cases r
  · exact check0
  · exact check1
  · exact check2
  · exact check3
  · exact check4
  · exact check5
  · exact check6
  · exact check7

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
public theorem cube_eq_one : localWitness 1 ^ 3 = 1 := by
  apply Held.eq_of_four_point_images
  decide +kernel

set_option maxRecDepth 16384 in
public theorem ne_one : localWitness 1 ≠ 1 := by
  have hm : representation (localWitness 1) (0 : Fin 2058) ≠ 0 := by decide +kernel
  intro he
  exact hm (by rw [he, map_one]; rfl)

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.Witness1
