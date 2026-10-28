module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.PackedData
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.Check

/-!
# Soundness of the packed permutation inverse checks

The Boolean tests check a square and a cube on ambient labels. Four adjacent
power-of-two intervals cover all 306936 labels; the padding uses reduction
modulo the degree. The numerical reductions are in `InverseCertificates`.
These checks certify permutations of the ambient set, not their comparison
with the original `WordSetup` permutations.

Source: ATLAS F24G1-p306936B0, GLS3 Table 5.3v; `source/generate_model.py`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel
open Certificate

/-- The raw bounded lookup used by the first permutation. -/
def rawA (i : Nat) : Nat := lookup blocksA i % 306936
/-- The raw bounded lookup used by the second permutation. -/
def rawB (i : Nat) : Nat := lookup blocksB i % 306936

def squareTest (i : Nat) : Bool :=
  let x := i % 306936
  rawA (rawA x) == x

def cubeTest (i : Nat) : Bool :=
  let x := i % 306936
  rawB (rawB (rawB x)) == x

/-- The four certified intervals cover the entire ambient set. -/
theorem covered_checks (f : Nat → Bool)
    (h₀ : checkPow f 0 18 = true)
    (h₁ : checkPow f 262144 15 = true)
    (h₂ : checkPow f 294912 13 = true)
    (h₃ : checkPow f 303104 12 = true)
    (i : Fin 306936) : f i.val = true := by
  by_cases h : i.val < 262144
  · exact checkPow_sound f 18 0 h₀ i.val (Nat.zero_le _) h
  by_cases h' : i.val < 294912
  · exact checkPow_sound f 15 262144 h₁ i.val (by omega) h'
  by_cases h'' : i.val < 303104
  · exact checkPow_sound f 13 294912 h₂ i.val (by omega) h''
  · exact checkPow_sound f 12 303104 h₃ i.val (by omega) (by omega)

theorem imageA_involutive_of_checks (h : ∀ i : Fin 306936, squareTest i.val = true) :
    Function.Involutive imageA := by
  intro i
  have hi := h i
  simp only [squareTest, Nat.mod_eq_of_lt i.isLt, beq_iff_eq] at hi
  exact Fin.ext hi

theorem imageB_cube_of_checks (h : ∀ i : Fin 306936, cubeTest i.val = true) :
    ∀ i, imageB (imageB (imageB i)) = i := by
  intro i
  have hi := h i
  simp only [cubeTest, Nat.mod_eq_of_lt i.isLt, beq_iff_eq] at hi
  exact Fin.ext hi

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel
