module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.PointChecks

/-!
# Numeric evaluation of the first stabilizer generators

The raw functions have exactly the values of word5 and word8 at every ambient
label. Four shorter word comparisons keep definitional checking shallow; the
two composition proofs combine them. `FixedPoints` consumes these identities
to evaluate the proposed stabilizer generators with ordinary kernel reduction.

Source: ATLAS F24G1-p306936B0 and the shared straight-line word definitions.
Reproduce with `StagesZeroTwo/source/fixed_points.py`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo

def rawWord3 (x : Nat) : Nat :=
  rawA (rawB (rawA (rawB (rawA (rawB (rawB (rawA (rawB (rawB (rawA (rawB (rawA (rawB (rawA (rawB (rawB (rawA (rawB (rawB (rawA (rawB (rawB (rawA (rawB (rawA (rawB (rawA (rawB (rawA (rawB (rawA (rawB (rawB (rawA (x)))))))))))))))))))))))))))))))))))

private theorem val_word3 (x : Fin 306936) :
    ((Word.word3 aPerm bPerm) x).val = rawWord3 x.val := rfl

def rawWord4Inv (x : Nat) : Nat :=
  rawA (rawB (rawB (rawB (rawB (rawA (rawB (rawB (rawB (rawB (rawA (rawB (rawB (rawA (rawB (rawB (rawA (rawB (rawB (rawA (rawB (rawB (rawA (rawB (rawB (rawA (rawB (rawB (rawA (rawB (rawB (rawA (rawB (rawB (rawB (rawB (rawA (rawB (rawB (rawB (rawB (rawA (rawB (rawB (rawB (rawB (rawA (rawB (rawB (rawA (rawB (rawB (rawB (rawB (x))))))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem val_word4 (x : Fin 306936) :
    ((Word.word4 aPerm bPerm)⁻¹ x).val = rawWord4Inv x.val := rfl

def rawWord6 (x : Nat) : Nat :=
  rawA (rawB (rawB (rawA (rawB (rawB (rawA (rawB (rawB (rawA (rawB (rawA (rawB (rawA (rawB (rawA (rawB (rawB (rawA (rawB (rawA (rawB (rawA (rawB (rawA (rawB (rawA (rawB (rawA (rawB (rawA (x)))))))))))))))))))))))))))))))

private theorem val_word6 (x : Fin 306936) :
    ((Word.word6 aPerm bPerm) x).val = rawWord6 x.val := rfl

def rawWord7Inv (x : Nat) : Nat :=
  rawA (rawB (rawB (rawB (rawB (rawA (rawB (rawB (rawA (rawB (rawB (rawA (rawB (rawB (rawA (rawB (rawB (rawB (rawB (rawA (rawB (rawB (rawB (rawB (rawA (rawB (rawB (rawA (rawB (rawB (rawB (rawB (rawA (rawB (rawB (rawB (rawB (rawA (rawB (rawB (rawA (rawB (rawB (rawB (rawB (rawA (rawB (rawB (rawB (rawB (x))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem val_word7 (x : Fin 306936) :
    ((Word.word7 aPerm bPerm)⁻¹ x).val = rawWord7Inv x.val := rfl

def rawWord5 (x : Nat) : Nat := rawWord3 (rawB (rawWord4Inv x))

/-- Numeric evaluation agrees at every ambient label. -/
theorem val_word5 (x : Fin 306936) :
    (Word.word5 aPerm bPerm x).val = rawWord5 x.val := by
  simp only [Word.word5, Equiv.Perm.mul_apply, val_word3,
    show ∀ y, (bPerm y).val = rawB y.val from fun _ => rfl,
    val_word4, rawWord5]

def rawWord8 (x : Nat) : Nat := rawWord6 (rawB (rawWord7Inv x))

/-- Numeric evaluation agrees at every ambient label. -/
theorem val_word8 (x : Fin 306936) :
    (Word.word8 aPerm bPerm x).val = rawWord8 x.val := by
  simp only [Word.word8, Equiv.Perm.mul_apply, val_word6,
    show ∀ y, (bPerm y).val = rawB y.val from fun _ => rfl,
    val_word7, rawWord8]

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo
