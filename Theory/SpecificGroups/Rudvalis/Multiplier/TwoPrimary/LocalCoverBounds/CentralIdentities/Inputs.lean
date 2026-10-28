module

public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.CentralIdentities.PowerCalculus

/-!
# Literal input equations for Rudvalis max4 central collection

The seven list words are exactly the powers and products of `Presentation.word`.
They evaluate to the seven central relators in the genuine quotient F/[F,R].
The inverse-letter correction follows from a² = r₀.

Source: `LocalCoverBounds/source/TwoGenerator.json`, derived from the marked
Wilson–Nickerson–Bray ATLAS max4 generators; Aschbacher–Smith I.1.3(1), p.407.
-/

@[expose] public section
namespace Rudvalis.Multiplier.TwoPrimary.LocalPresentation.CentralKernel.IdentityReplay

def alphabet : Fin 3 → Central :=
  ![centralGenerator false, centralGenerator true, (centralGenerator true)⁻¹]

theorem alphabet_inverse (i : Fin 3) :
    alphabet (inverseLetter i) = (alphabet i)⁻¹ * (centralRelator 0 : Central) ^
      (if i = 0 then 1 else 0 : ℕ) := by
  fin_cases i
  · change centralGenerator false = (centralGenerator false)⁻¹ * (centralRelator 0 : Central)
    rw [centralRelator_val]
    change centralGenerator false = (centralGenerator false)⁻¹ * centralGenerator false ^ 2
    group
  · simp [alphabet, inverseLetter]
  · simp [alphabet, inverseLetter]

def sourceWord : Fin 7 → List (Fin 3) :=
  ![[0, 0],
    [1, 1, 1],
    [0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1],
    [2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0],
    [0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2],
    [1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0],
    [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2]]

def sourceExponent (i : Fin 7) : Fin 7 → ℤ := fun j => if j = i then 1 else 0

theorem collect_sourceExponent (i : Fin 7) : collect (sourceExponent i) = centralRelator i := by
  fin_cases i <;> simp [collect, sourceExponent]

theorem source_relation_0 : Eqn alphabet (sourceWord 0) [] (sourceExponent 0) := by
  simp only [Eqn, readWord_nil, one_mul, collect_sourceExponent]
  rw [centralRelator_val]
  simp [sourceWord, word, alphabet, readWord_cons, readWord_nil, pow_succ, mul_assoc]

theorem source_relation_1 : Eqn alphabet (sourceWord 1) [] (sourceExponent 1) := by
  simp only [Eqn, readWord_nil, one_mul, collect_sourceExponent]
  rw [centralRelator_val]
  simp [sourceWord, word, alphabet, readWord_cons, readWord_nil, pow_succ, mul_assoc]

theorem source_relation_2 : Eqn alphabet (sourceWord 2) [] (sourceExponent 2) := by
  simp only [Eqn, readWord_nil, one_mul, collect_sourceExponent]
  rw [centralRelator_val]
  simp [sourceWord, word, alphabet, readWord_cons, readWord_nil, pow_succ, mul_assoc]

theorem source_relation_3 : Eqn alphabet (sourceWord 3) [] (sourceExponent 3) := by
  simp only [Eqn, readWord_nil, one_mul, collect_sourceExponent]
  rw [centralRelator_val]
  simp [sourceWord, word, alphabet, readWord_cons, readWord_nil, pow_succ, mul_assoc]

theorem source_relation_4 : Eqn alphabet (sourceWord 4) [] (sourceExponent 4) := by
  simp only [Eqn, readWord_nil, one_mul, collect_sourceExponent]
  rw [centralRelator_val]
  simp [sourceWord, word, alphabet, readWord_cons, readWord_nil, pow_succ, mul_assoc]

theorem source_relation_5 : Eqn alphabet (sourceWord 5) [] (sourceExponent 5) := by
  simp only [Eqn, readWord_nil, one_mul, collect_sourceExponent]
  rw [centralRelator_val]
  simp [sourceWord, word, alphabet, readWord_cons, readWord_nil, pow_succ, mul_assoc]

theorem source_relation_6 : Eqn alphabet (sourceWord 6) [] (sourceExponent 6) := by
  simp only [Eqn, readWord_nil, one_mul, collect_sourceExponent]
  rw [centralRelator_val]
  simp [sourceWord, word, alphabet, readWord_cons, readWord_nil, pow_succ, mul_assoc]

theorem source_relation (i : Fin 7) : Eqn alphabet (sourceWord i) [] (sourceExponent i) := by
  fin_cases i
  · exact source_relation_0
  · exact source_relation_1
  · exact source_relation_2
  · exact source_relation_3
  · exact source_relation_4
  · exact source_relation_5
  · exact source_relation_6

end Rudvalis.Multiplier.TwoPrimary.LocalPresentation.CentralKernel.IdentityReplay
