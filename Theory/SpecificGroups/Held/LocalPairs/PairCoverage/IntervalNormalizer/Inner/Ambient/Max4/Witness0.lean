module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.LocalWords

/-! Kernel-checked conjugation and order identities for the literal max4
local witness 0. See `LocalWords` for source attribution and word conventions. -/

namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.Witness0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem check0 : ∀ x : Fin 4,
    representation (localWitness 0 * schreierGenerator (largeRow 0) 0 * (localWitness 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (evalSchreierWord (largeRow 0) (conjugateWord 0 0))
      ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem check1 : ∀ x : Fin 4,
    representation (localWitness 0 * schreierGenerator (largeRow 0) 1 * (localWitness 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (evalSchreierWord (largeRow 0) (conjugateWord 0 1))
      ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem check2 : ∀ x : Fin 4,
    representation (localWitness 0 * schreierGenerator (largeRow 0) 2 * (localWitness 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (evalSchreierWord (largeRow 0) (conjugateWord 0 2))
      ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem check3 : ∀ x : Fin 4,
    representation (localWitness 0 * schreierGenerator (largeRow 0) 3 * (localWitness 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (evalSchreierWord (largeRow 0) (conjugateWord 0 3))
      ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem check4 : ∀ x : Fin 4,
    representation (localWitness 0 * schreierGenerator (largeRow 0) 4 * (localWitness 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (evalSchreierWord (largeRow 0) (conjugateWord 0 4))
      ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem check5 : ∀ x : Fin 4,
    representation (localWitness 0 * schreierGenerator (largeRow 0) 5 * (localWitness 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (evalSchreierWord (largeRow 0) (conjugateWord 0 5))
      ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem check6 : ∀ x : Fin 4,
    representation (localWitness 0 * schreierGenerator (largeRow 0) 6 * (localWitness 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (evalSchreierWord (largeRow 0) (conjugateWord 0 6))
      ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem check7 : ∀ x : Fin 4,
    representation (localWitness 0 * schreierGenerator (largeRow 0) 7 * (localWitness 0)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (evalSchreierWord (largeRow 0) (conjugateWord 0 7))
      ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
public theorem conjugate_eq (r : Fin 8) :
    localWitness 0 * schreierGenerator (largeRow 0) r * (localWitness 0)⁻¹ =
      evalSchreierWord (largeRow 0) (conjugateWord 0 r) := by
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
public theorem cube_eq_one : localWitness 0 ^ 3 = 1 := by
  apply Held.eq_of_four_point_images
  decide +kernel

set_option maxRecDepth 16384 in
public theorem ne_one : localWitness 0 ≠ 1 := by
  have hm : representation (localWitness 0) (2 : Fin 2058) ≠ 2 := by decide +kernel
  intro he
  exact hm (by rw [he, map_one]; rfl)

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.Witness0
