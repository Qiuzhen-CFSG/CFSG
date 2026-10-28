module
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.LongWords.Bridge
public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.LongWords.Replay.Output

/-!
# Applying the checked long-word replay to the literal local generators

The two extra bridge premises are the auxiliary-generator coordinate and the
seventeen-letter relation. All seven replay inputs are constructed here from
those premises and the explicitly stated short relations. No finiteness or
model comparison occurs in this argument.
-/

@[expose] public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.LongWords
variable {G : Type*} [Group G]

/-- The exact algebraic input to the small word replay. -/
def replayInputs (a c t : G)
    (hx : a ^ 2 = 1) (hc : c ^ 4 = 1) (h6 : (a * c⁻¹) ^ 6 = 1)
    (h3 : (a * t⁻¹) ^ 3 = 1)
    (hcomm : a * c * t⁻¹ * a * t * c⁻¹ = 1)
    (h4 : (c⁻¹ * a * t⁻¹ * a) ^ 4 = 1)
    (h17 : seventeenWord a c t = 1)
    (ht : t = coordinateWord a c) : Replay.Inputs G := by
  let g := letters a c
  have hxx : a * a = 1 := by simpa only [pow_two] using hx
  have hxi : a⁻¹ = a := inv_eq_of_mul_eq_one_right hxx
  have hi := letters_inverse a c hx
  have cancel_aa : readWord g [0, 0] = readWord g [] := by simp [g, letters, hxx]
  have cancel_bB : readWord g [1, 2] = readWord g [] := by simp [g, letters]
  have cancel_Bb : readWord g [2, 1] = readWord g [] := by simp [g, letters]
  refine ⟨g, hi, ?_⟩
  intro n
  rcases n with _ | (_ | (_ | (_ | (_ | (_ | (_ | n))))))
  · simpa [Replay.sourceWord, g, letters, pow_two] using hx
  · simpa [Replay.sourceWord, g, letters, pow_succ, mul_assoc] using hc
  · simpa [Replay.sourceWord, g, letters, pow_succ, mul_assoc] using h6
  · have hh := h3
    rw [ht] at hh
    have raw : readWord g [0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] = 1 := by
      simpa only [readWord_cons, readWord_nil, g, letters, coordinateWord, seventeenWord,
        pow_succ, pow_zero, mul_one, mul_inv_rev, inv_inv, inv_one, one_mul, hxi, mul_assoc] using hh
    have e : readWord g [0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] = readWord g [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] :=
      (context g [] [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] [0, 0] [] cancel_aa).trans ((context g [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] [0, 0] [] cancel_aa).trans (context g [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] [0, 0] [] cancel_aa))
    exact e.symm.trans raw
  · have hh := hcomm
    rw [ht] at hh
    have raw : readWord g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 2] = 1 := by
      simpa only [readWord_cons, readWord_nil, g, letters, coordinateWord, seventeenWord,
        pow_succ, pow_zero, mul_one, mul_inv_rev, inv_inv, inv_one, one_mul, hxi, mul_assoc] using hh
    have e : readWord g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 2] = readWord g [0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 2] :=
      rfl
    exact e.symm.trans raw
  · have hh := h4
    rw [ht] at hh
    have raw : readWord g [2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] = 1 := by
      simpa only [readWord_cons, readWord_nil, g, letters, coordinateWord, seventeenWord,
        pow_succ, pow_zero, mul_one, mul_inv_rev, inv_inv, inv_one, one_mul, hxi, mul_assoc] using hh
    have e : readWord g [2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] = readWord g [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] :=
      (context g [2] [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] [0, 0] [] cancel_aa).trans ((context g [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] [0, 0] [] cancel_aa).trans ((context g [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] [0, 0] [] cancel_aa).trans (context g [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2] [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0] [0, 0] [] cancel_aa)))
    exact e.symm.trans raw
  · have hh := h17
    rw [ht] at hh
    have raw : readWord g [2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 1, 0, 2, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 2, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0] = 1 := by
      simpa only [readWord_cons, readWord_nil, g, letters, coordinateWord, seventeenWord,
        pow_succ, pow_zero, mul_one, mul_inv_rev, inv_inv, inv_one, one_mul, hxi, mul_assoc] using hh
    have e : readWord g [2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 1, 0, 2, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 2, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0] = readWord g [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0] :=
      (context g [2] [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 1, 0, 2, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 2, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0] [0, 0] [] cancel_aa).trans ((context g [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2] [2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 1, 0, 2, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 2, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0] [0, 0] [] cancel_aa).trans ((context g [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2] [0, 2, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 2, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0] [2, 1] [] cancel_Bb).trans ((context g [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0] [1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 2, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0] [2, 1] [] cancel_Bb).trans ((context g [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1] [1, 0, 2, 1, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0] [0, 0] [] cancel_aa).trans ((context g [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0] [1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0] [2, 1] [] cancel_Bb).trans (context g [2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 2, 2, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1] [1, 0] [0, 0] [] cancel_aa))))))
    exact e.symm.trans raw
  · simp [Replay.sourceWord, readWord_nil]

/-- All three local relators follow from the two bridge identities. -/
theorem long_relations_of_bridge_inputs (a c t : G)
    (hx : a ^ 2 = 1) (hc : c ^ 4 = 1) (h6 : (a * c⁻¹) ^ 6 = 1)
    (h3 : (a * t⁻¹) ^ 3 = 1)
    (hcomm : a * c * t⁻¹ * a * t * c⁻¹ = 1)
    (h4 : (c⁻¹ * a * t⁻¹ * a) ^ 4 = 1)
    (h17 : seventeenWord a c t = 1)
    (ht : t = coordinateWord a c) :
    ∀ i : Fin 3, LocalPresentation.relator a c ⟨i.val + 3, by omega⟩ = 1 := by
  let P := replayInputs a c t hx hc h6 h3 hcomm h4 h17 ht
  intro i
  fin_cases i
  · have hh := Replay.output_0 P
    change readWord (letters a c) [0, 2, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 2, 0, 1, 0, 2, 2] = 1 at hh
    simpa only [readWord_cons, readWord_nil, letters,
      LocalPresentation.relator, pow_succ, pow_zero, mul_one, one_mul, mul_assoc] using hh
  · have hh := Replay.output_1 P
    change readWord (letters a c) [2, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0] = 1 at hh
    simpa only [readWord_cons, readWord_nil, letters,
      LocalPresentation.relator, pow_succ, pow_zero, mul_one, one_mul, mul_assoc] using hh
  · have hh := Replay.output_2 P
    change readWord (letters a c) [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2] = 1 at hh
    simpa only [readWord_cons, readWord_nil, letters,
      LocalPresentation.relator, pow_succ, pow_zero, mul_one, one_mul, mul_assoc] using hh
end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Finite.Relations.LongWords
