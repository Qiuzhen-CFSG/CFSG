module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.OverlapExtensions.CentralExtensions.Edges
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.OverlapExtensions.CentralExtensions.WordLift
public import Theory.GroupTheory.CentralInvolutionTwist

/-!
# Two binary characters of the genuine first endpoint

Parity of the occurrences of the second and third generators respects every
certified right Cayley edge. The finite-word lifting lemma therefore gives
two actual homomorphisms from `firstParabolic`. Both kill the central mark,
since it is the square of the first generator. The generator equations retain
the literal left inclusion of the verified amalgam.

This supplies the characters used in the central extensions for the corrected
outer M₁₂ amalgam. Source context and degree-24 ATLAS attribution are retained
from `CentralExtensions.Coordinates` and `Extension.Seeds`.
-/
@[expose] public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.OverlapExtensions
set_option maxRecDepth 100000
-- Bound temporary memory while checking the finite parity certificates.
set_option Elab.async false
namespace Endpoint
open Theory.GroupTheory.CentralInvolutionTwist

/-- Occurrence parity of the second or third generator in a chosen endpoint word. -/
def wordParity (k : Fin 2) (i : Fin 384) : C2 :=
  Multiplicative.ofAdd ((Data.endpointWordTable[i.val]!).count (k.val + 1) : ZMod 2)

def generatorParity (k : Fin 2) (j : Fin 4) : C2 :=
  if j.val = k.val + 1 then Multiplicative.ofAdd 1 else 1

private theorem wordParity_zero (k : Fin 2) : wordParity k 0 = 1 := by
  fin_cases k <;> rfl

private theorem parity_0 : ∀ (k : Fin 2) (i : Fin 16) (j : Fin 4),
    wordParity k (Data.endpointStep (⟨0 + i.val, by omega⟩) j) = wordParity k (⟨0 + i.val, by omega⟩) * generatorParity k j := by decide +kernel

private theorem parity_1 : ∀ (k : Fin 2) (i : Fin 16) (j : Fin 4),
    wordParity k (Data.endpointStep (⟨16 + i.val, by omega⟩) j) = wordParity k (⟨16 + i.val, by omega⟩) * generatorParity k j := by decide +kernel

private theorem parity_2 : ∀ (k : Fin 2) (i : Fin 16) (j : Fin 4),
    wordParity k (Data.endpointStep (⟨32 + i.val, by omega⟩) j) = wordParity k (⟨32 + i.val, by omega⟩) * generatorParity k j := by decide +kernel

private theorem parity_3 : ∀ (k : Fin 2) (i : Fin 16) (j : Fin 4),
    wordParity k (Data.endpointStep (⟨48 + i.val, by omega⟩) j) = wordParity k (⟨48 + i.val, by omega⟩) * generatorParity k j := by decide +kernel

private theorem parity_4 : ∀ (k : Fin 2) (i : Fin 16) (j : Fin 4),
    wordParity k (Data.endpointStep (⟨64 + i.val, by omega⟩) j) = wordParity k (⟨64 + i.val, by omega⟩) * generatorParity k j := by decide +kernel

private theorem parity_5 : ∀ (k : Fin 2) (i : Fin 16) (j : Fin 4),
    wordParity k (Data.endpointStep (⟨80 + i.val, by omega⟩) j) = wordParity k (⟨80 + i.val, by omega⟩) * generatorParity k j := by decide +kernel

private theorem parity_6 : ∀ (k : Fin 2) (i : Fin 16) (j : Fin 4),
    wordParity k (Data.endpointStep (⟨96 + i.val, by omega⟩) j) = wordParity k (⟨96 + i.val, by omega⟩) * generatorParity k j := by decide +kernel

private theorem parity_7 : ∀ (k : Fin 2) (i : Fin 16) (j : Fin 4),
    wordParity k (Data.endpointStep (⟨112 + i.val, by omega⟩) j) = wordParity k (⟨112 + i.val, by omega⟩) * generatorParity k j := by decide +kernel

private theorem parity_8 : ∀ (k : Fin 2) (i : Fin 16) (j : Fin 4),
    wordParity k (Data.endpointStep (⟨128 + i.val, by omega⟩) j) = wordParity k (⟨128 + i.val, by omega⟩) * generatorParity k j := by decide +kernel

private theorem parity_9 : ∀ (k : Fin 2) (i : Fin 16) (j : Fin 4),
    wordParity k (Data.endpointStep (⟨144 + i.val, by omega⟩) j) = wordParity k (⟨144 + i.val, by omega⟩) * generatorParity k j := by decide +kernel

private theorem parity_10 : ∀ (k : Fin 2) (i : Fin 16) (j : Fin 4),
    wordParity k (Data.endpointStep (⟨160 + i.val, by omega⟩) j) = wordParity k (⟨160 + i.val, by omega⟩) * generatorParity k j := by decide +kernel

private theorem parity_11 : ∀ (k : Fin 2) (i : Fin 16) (j : Fin 4),
    wordParity k (Data.endpointStep (⟨176 + i.val, by omega⟩) j) = wordParity k (⟨176 + i.val, by omega⟩) * generatorParity k j := by decide +kernel

private theorem parity_12 : ∀ (k : Fin 2) (i : Fin 16) (j : Fin 4),
    wordParity k (Data.endpointStep (⟨192 + i.val, by omega⟩) j) = wordParity k (⟨192 + i.val, by omega⟩) * generatorParity k j := by decide +kernel

private theorem parity_13 : ∀ (k : Fin 2) (i : Fin 16) (j : Fin 4),
    wordParity k (Data.endpointStep (⟨208 + i.val, by omega⟩) j) = wordParity k (⟨208 + i.val, by omega⟩) * generatorParity k j := by decide +kernel

private theorem parity_14 : ∀ (k : Fin 2) (i : Fin 16) (j : Fin 4),
    wordParity k (Data.endpointStep (⟨224 + i.val, by omega⟩) j) = wordParity k (⟨224 + i.val, by omega⟩) * generatorParity k j := by decide +kernel

private theorem parity_15 : ∀ (k : Fin 2) (i : Fin 16) (j : Fin 4),
    wordParity k (Data.endpointStep (⟨240 + i.val, by omega⟩) j) = wordParity k (⟨240 + i.val, by omega⟩) * generatorParity k j := by decide +kernel

private theorem parity_16 : ∀ (k : Fin 2) (i : Fin 16) (j : Fin 4),
    wordParity k (Data.endpointStep (⟨256 + i.val, by omega⟩) j) = wordParity k (⟨256 + i.val, by omega⟩) * generatorParity k j := by decide +kernel

private theorem parity_17 : ∀ (k : Fin 2) (i : Fin 16) (j : Fin 4),
    wordParity k (Data.endpointStep (⟨272 + i.val, by omega⟩) j) = wordParity k (⟨272 + i.val, by omega⟩) * generatorParity k j := by decide +kernel

private theorem parity_18 : ∀ (k : Fin 2) (i : Fin 16) (j : Fin 4),
    wordParity k (Data.endpointStep (⟨288 + i.val, by omega⟩) j) = wordParity k (⟨288 + i.val, by omega⟩) * generatorParity k j := by decide +kernel

private theorem parity_19 : ∀ (k : Fin 2) (i : Fin 16) (j : Fin 4),
    wordParity k (Data.endpointStep (⟨304 + i.val, by omega⟩) j) = wordParity k (⟨304 + i.val, by omega⟩) * generatorParity k j := by decide +kernel

private theorem parity_20 : ∀ (k : Fin 2) (i : Fin 16) (j : Fin 4),
    wordParity k (Data.endpointStep (⟨320 + i.val, by omega⟩) j) = wordParity k (⟨320 + i.val, by omega⟩) * generatorParity k j := by decide +kernel

private theorem parity_21 : ∀ (k : Fin 2) (i : Fin 16) (j : Fin 4),
    wordParity k (Data.endpointStep (⟨336 + i.val, by omega⟩) j) = wordParity k (⟨336 + i.val, by omega⟩) * generatorParity k j := by decide +kernel

private theorem parity_22 : ∀ (k : Fin 2) (i : Fin 16) (j : Fin 4),
    wordParity k (Data.endpointStep (⟨352 + i.val, by omega⟩) j) = wordParity k (⟨352 + i.val, by omega⟩) * generatorParity k j := by decide +kernel

private theorem parity_23 : ∀ (k : Fin 2) (i : Fin 16) (j : Fin 4),
    wordParity k (Data.endpointStep (⟨368 + i.val, by omega⟩) j) = wordParity k (⟨368 + i.val, by omega⟩) * generatorParity k j := by decide +kernel

private theorem parity_block (b : Fin 24) : ∀ (k : Fin 2) (i : Fin 16) (j : Fin 4),
    wordParity k (Data.endpointStep ⟨16 * b.val + i.val, by omega⟩ j) =
      wordParity k ⟨16 * b.val + i.val, by omega⟩ * generatorParity k j := by
  fin_cases b
  · exact parity_0
  · exact parity_1
  · exact parity_2
  · exact parity_3
  · exact parity_4
  · exact parity_5
  · exact parity_6
  · exact parity_7
  · exact parity_8
  · exact parity_9
  · exact parity_10
  · exact parity_11
  · exact parity_12
  · exact parity_13
  · exact parity_14
  · exact parity_15
  · exact parity_16
  · exact parity_17
  · exact parity_18
  · exact parity_19
  · exact parity_20
  · exact parity_21
  · exact parity_22
  · exact parity_23

private theorem wordParity_step (k : Fin 2) (i : Fin 384) (j : Fin 4) :
    wordParity k (Data.endpointStep i j) = wordParity k i * generatorParity k j := by
  have h := parity_block ⟨i.val / 16, by omega⟩ k ⟨i.val % 16, by omega⟩ j
  have e : (⟨16 * (i.val / 16) + i.val % 16, by omega⟩ : Fin 384) = i := by
    apply Fin.ext
    change 16 * (i.val / 16) + i.val % 16 = i.val
    omega
  exact e ▸ h

/-- The two independent parity characters on the genuine first endpoint. -/
noncomputable def character (k : Fin 2) : firstParabolic →* C2 :=
  FiniteWords.lift generator Data.endpointWords coordinates (fun _ => rfl)
    0 element_zero Data.endpointStep element_step
    (wordParity k) (generatorParity k)
    (by exact wordParity_zero k) (by exact wordParity_step k)

theorem character_element (k : Fin 2) (i : Fin 384) :
    character k (element i) = wordParity k i :=
  FiniteWords.lift_element generator Data.endpointWords coordinates (fun _ => rfl)
    0 element_zero Data.endpointStep element_step
    (wordParity k) (generatorParity k) (wordParity_zero k) (wordParity_step k) i

theorem character_generator (k : Fin 2) (j : Fin 4) :
    character k (generator j) = generatorParity k j := by
  rw [← element_generator j, character_element]
  fin_cases k <;> fin_cases j <;> decide +kernel

/-- The endpoint generating tuple retains the literal overlap inclusion. -/
theorem left_generator (j : Fin 3) :
    VerifiedPair.amalgam.left (Overlap.generator j) = generator ⟨j.val, by omega⟩ := by
  fin_cases j <;> rfl

theorem character_overlap_generator (k : Fin 2) (j : Fin 3) :
    character k (VerifiedPair.amalgam.left (Overlap.generator j)) =
      if j.val = k.val + 1 then Multiplicative.ofAdd 1 else 1 := by
  rw [left_generator, character_generator]
  rfl

theorem character_marked (k : Fin 2) :
    character k (VerifiedPair.amalgam.left marked) = 1 := by
  rw [marked, map_pow, map_pow, character_overlap_generator]
  fin_cases k <;> decide +kernel

end Endpoint

end Sporadic.Mathieu.M12ExceptionalExtension.OverlapExtensions
