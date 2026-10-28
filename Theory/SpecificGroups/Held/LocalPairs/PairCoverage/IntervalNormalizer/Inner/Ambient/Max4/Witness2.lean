module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.LocalWords

/-! Kernel-checked conjugation and order identities for the literal max4
local witness 2. See `LocalWords` for source attribution and word conventions. -/

namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.Witness2

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem check0 : ∀ x : Fin 4,
    representation (localWitness 2 * schreierGenerator (largeRow 2) 0 * (localWitness 2)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (evalSchreierWord (largeRow 2) (conjugateWord 2 0))
      ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem check1 : ∀ x : Fin 4,
    representation (localWitness 2 * schreierGenerator (largeRow 2) 1 * (localWitness 2)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (evalSchreierWord (largeRow 2) (conjugateWord 2 1))
      ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem check2 : ∀ x : Fin 4,
    representation (localWitness 2 * schreierGenerator (largeRow 2) 2 * (localWitness 2)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (evalSchreierWord (largeRow 2) (conjugateWord 2 2))
      ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem check3 : ∀ x : Fin 4,
    representation (localWitness 2 * schreierGenerator (largeRow 2) 3 * (localWitness 2)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (evalSchreierWord (largeRow 2) (conjugateWord 2 3))
      ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem check4 : ∀ x : Fin 4,
    representation (localWitness 2 * schreierGenerator (largeRow 2) 4 * (localWitness 2)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (evalSchreierWord (largeRow 2) (conjugateWord 2 4))
      ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem check5 : ∀ x : Fin 4,
    representation (localWitness 2 * schreierGenerator (largeRow 2) 5 * (localWitness 2)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (evalSchreierWord (largeRow 2) (conjugateWord 2 5))
      ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem check6 : ∀ x : Fin 4,
    representation (localWitness 2 * schreierGenerator (largeRow 2) 6 * (localWitness 2)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (evalSchreierWord (largeRow 2) (conjugateWord 2 6))
      ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem check7 : ∀ x : Fin 4,
    representation (localWitness 2 * schreierGenerator (largeRow 2) 7 * (localWitness 2)⁻¹)
      ⟨x.val, by omega⟩ =
    representation (evalSchreierWord (largeRow 2) (conjugateWord 2 7))
      ⟨x.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16384 in
public theorem conjugate_eq (r : Fin 8) :
    localWitness 2 * schreierGenerator (largeRow 2) r * (localWitness 2)⁻¹ =
      evalSchreierWord (largeRow 2) (conjugateWord 2 r) := by
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
public theorem cube_eq_one : localWitness 2 ^ 3 = 1 := by
  apply Held.eq_of_four_point_images
  decide +kernel

set_option maxRecDepth 16384 in
public theorem ne_one : localWitness 2 ≠ 1 := by
  have hm : representation (localWitness 2) (0 : Fin 2058) ≠ 0 := by decide +kernel
  intro he
  exact hm (by rw [he, map_one]; rfl)

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Ambient.Max4.Witness2
