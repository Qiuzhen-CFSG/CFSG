module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection.PowerIdentities.WordCalculus

/-!
# Literal source inputs for the central word certificate

The alphabet is a, b, b⁻¹ in the genuine free central extension. The seven
equations below are proved from `centralRelator_val`; they add no hypothesis.

Source: Wilson–Nickerson–Bray, ATLAS `S62G1-P1.M`.
See `PowerIdentities/source/README.md` for the trace and conventions.
-/

@[expose] public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection.PowerReplay


def alphabet : Fin 3 → Central :=
  ![centralGenerator false, centralGenerator true, (centralGenerator true)⁻¹]

theorem alphabet_inverse (i : Fin 3) :
    alphabet (inverseLetter i) = (alphabet i)⁻¹ * (centralRelator 0 : Central) ^
      (if i = 0 then 1 else 0 : ℕ) := by
  fin_cases i
  · change centralGenerator false = (centralGenerator false)⁻¹ *
      (centralRelator 0 : Central)
    rw [centralRelator_val]
    change centralGenerator false = (centralGenerator false)⁻¹ * (centralGenerator false) ^ 2
    group
  · simp [alphabet, inverseLetter]
  · simp [alphabet, inverseLetter]


def sourceWord (i : Fin 7) : List (Fin 3) :=
  match i.val with
  | 0 => [0, 0]
  | 1 => [1, 1, 1, 1, 1, 1, 1]
  | 2 => [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
  | 3 => [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1]
  | 4 => [0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1]
  | 5 => [0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1]
  | 6 => [0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1]
  | _ => []

def sourceExponent (i : Fin 7) : Fin 7 → ℤ :=
  match i.val with
  | 0 => ![1, 0, 0, 0, 0, 0, 0]
  | 1 => ![0, 1, 0, 0, 0, 0, 0]
  | 2 => ![0, 0, 1, 0, 0, 0, 0]
  | 3 => ![0, 0, 0, 1, 0, 0, 0]
  | 4 => ![6, 0, 0, 0, 1, 0, 0]
  | 5 => ![3, 0, 0, 0, 0, 1, 0]
  | 6 => ![2, 0, 0, 0, 0, 0, 1]
  | _ => 0

theorem source_relation_0 : Eqn alphabet (sourceWord 0) [] (sourceExponent 0) := by
  have he : collect (sourceExponent 0) = centralRelator 0 := by simp [collect, sourceExponent]
  simp only [Eqn, readWord_nil, one_mul, he]
  rw [centralRelator_val]
  change readWord alphabet [0, 0] = centralGenerator false ^ 2
  simp only [alphabet, readWord_cons, readWord_nil, pow_succ, pow_zero, one_mul, mul_one, Matrix.cons_val_zero]

theorem source_relation_1 : Eqn alphabet (sourceWord 1) [] (sourceExponent 1) := by
  have he : collect (sourceExponent 1) = centralRelator 1 := by simp [collect, sourceExponent]
  simp only [Eqn, readWord_nil, one_mul, he]
  rw [centralRelator_val]
  change readWord alphabet [1, 1, 1, 1, 1, 1, 1] = centralGenerator true ^ 7
  simp only [alphabet, readWord_cons, readWord_nil, pow_succ, pow_zero, one_mul, mul_one, mul_assoc, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem source_relation_2 : Eqn alphabet (sourceWord 2) [] (sourceExponent 2) := by
  have he : collect (sourceExponent 2) = centralRelator 2 := by simp [collect, sourceExponent]
  simp only [Eqn, readWord_nil, one_mul, he]
  rw [centralRelator_val]
  change readWord alphabet [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] = (centralGenerator false * centralGenerator true) ^ 9
  simp only [alphabet, readWord_cons, readWord_nil, pow_succ, pow_zero, one_mul, mul_one, mul_assoc, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem source_relation_3 : Eqn alphabet (sourceWord 3) [] (sourceExponent 3) := by
  have he : collect (sourceExponent 3) = centralRelator 3 := by simp [collect, sourceExponent]
  simp only [Eqn, readWord_nil, one_mul, he]
  rw [centralRelator_val]
  change readWord alphabet [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] = (centralGenerator false * centralGenerator true ^ 2) ^ 12
  simp only [alphabet, readWord_cons, readWord_nil, pow_succ, pow_zero, one_mul, mul_one, mul_assoc, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem source_relation_4 : Eqn alphabet (sourceWord 4) [] (sourceExponent 4) := by
    have hl : readWord alphabet (sourceWord 4) =
        readWord alphabet (commWord [1, 0, 1, 0, 1]) ^ 2 := by
      simp [sourceWord, commWord, inverseWord, inverseLetter, readWord_cons,
        readWord_nil, pow_succ, mul_assoc]
    have hr : sourceCommutator (alphabet 0) (readWord alphabet [1, 0, 1, 0, 1]) ^ 2 =
        (centralRelator 4 : Central) := by
      simpa [alphabet, readWord_cons, readWord_nil, word, sourceCommutator, mul_assoc,
        pow_succ] using (centralRelator_val 4).symm
    dsimp only [Eqn]
    rw [hl, readWord_commWord_pow alphabet (centralRelator 0) alphabet_inverse, hr]
    change (centralRelator 4 : Central) * (centralRelator 0 : Central) ^ 6 = _
    simpa [collect, sourceExponent] using
      (Subgroup.mem_center_iff.mp (centralRelator 4).property
        ((centralRelator 0 : Central) ^ 6)).symm
theorem source_relation_5 : Eqn alphabet (sourceWord 5) [] (sourceExponent 5) := by
    have hl : readWord alphabet (sourceWord 5) =
        readWord alphabet (commWord [1]) ^ 3 := by
      simp [sourceWord, commWord, inverseWord, inverseLetter, readWord_cons,
        readWord_nil, pow_succ, mul_assoc]
    have hr : sourceCommutator (alphabet 0) (readWord alphabet [1]) ^ 3 =
        (centralRelator 5 : Central) := by
      simpa [alphabet, readWord_cons, readWord_nil, word, sourceCommutator, mul_assoc,
        pow_succ] using (centralRelator_val 5).symm
    dsimp only [Eqn]
    rw [hl, readWord_commWord_pow alphabet (centralRelator 0) alphabet_inverse, hr]
    change (centralRelator 5 : Central) * (centralRelator 0 : Central) ^ 3 = _
    simpa [collect, sourceExponent] using
      (Subgroup.mem_center_iff.mp (centralRelator 5).property
        ((centralRelator 0 : Central) ^ 3)).symm
theorem source_relation_6 : Eqn alphabet (sourceWord 6) [] (sourceExponent 6) := by
    have hl : readWord alphabet (sourceWord 6) =
        readWord alphabet (commWord [1, 1]) ^ 2 := by
      simp [sourceWord, commWord, inverseWord, inverseLetter, readWord_cons,
        readWord_nil, pow_succ, mul_assoc]
    have hr : sourceCommutator (alphabet 0) (readWord alphabet [1, 1]) ^ 2 =
        (centralRelator 6 : Central) := by
      simpa [alphabet, readWord_cons, readWord_nil, word, sourceCommutator, mul_assoc,
        pow_succ] using (centralRelator_val 6).symm
    dsimp only [Eqn]
    rw [hl, readWord_commWord_pow alphabet (centralRelator 0) alphabet_inverse, hr]
    change (centralRelator 6 : Central) * (centralRelator 0 : Central) ^ 2 = _
    simpa [collect, sourceExponent] using
      (Subgroup.mem_center_iff.mp (centralRelator 6).property
        ((centralRelator 0 : Central) ^ 2)).symm

theorem source_relation (i : Fin 7) : Eqn alphabet (sourceWord i) [] (sourceExponent i) := by
  fin_cases i
  · exact source_relation_0
  · exact source_relation_1
  · exact source_relation_2
  · exact source_relation_3
  · exact source_relation_4
  · exact source_relation_5
  · exact source_relation_6

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection.PowerReplay
