module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PositiveWords

/-!
# Exact multiplication circuit for the six long HS words

The circuit shares repeated ordered subwords, without using any group relation.
The six endpoint equalities below hold in every monoid and retain every letter
of PositiveWords, including R1--R3. Product certificates are supplied separately.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords

def word00 {M : Type*} [Monoid M] (a _b : M) : M := a
def word01 {M : Type*} [Monoid M] (_a b : M) : M := b

def word02 {M : Type*} [Monoid M] (a b : M) : M := word01 a b * word01 a b
def word03 {M : Type*} [Monoid M] (a b : M) : M := word00 a b * word02 a b
def word04 {M : Type*} [Monoid M] (a b : M) : M := word00 a b * word01 a b
def word05 {M : Type*} [Monoid M] (a b : M) : M := word04 a b * word03 a b
def word06 {M : Type*} [Monoid M] (a b : M) : M := word04 a b * word05 a b
def word07 {M : Type*} [Monoid M] (a b : M) : M := word03 a b * word01 a b
def word08 {M : Type*} [Monoid M] (a b : M) : M := word03 a b * word02 a b
def word09 {M : Type*} [Monoid M] (a b : M) : M := word06 a b * word08 a b
def word10 {M : Type*} [Monoid M] (a b : M) : M := word07 a b * word07 a b
def word11 {M : Type*} [Monoid M] (a b : M) : M := word06 a b * word02 a b
def word12 {M : Type*} [Monoid M] (a b : M) : M := word09 a b * word07 a b
def word13 {M : Type*} [Monoid M] (a b : M) : M := word08 a b * word03 a b
def word14 {M : Type*} [Monoid M] (a b : M) : M := word06 a b * word01 a b
def word15 {M : Type*} [Monoid M] (a b : M) : M := word10 a b * word03 a b
def word16 {M : Type*} [Monoid M] (a b : M) : M := word06 a b * word03 a b
def word17 {M : Type*} [Monoid M] (a b : M) : M := word05 a b * word02 a b
def word18 {M : Type*} [Monoid M] (a b : M) : M := word12 a b * word11 a b
def word19 {M : Type*} [Monoid M] (a b : M) : M := word12 a b * word13 a b
def word20 {M : Type*} [Monoid M] (a b : M) : M := word14 a b * word10 a b
def word21 {M : Type*} [Monoid M] (a b : M) : M := word19 a b * word20 a b
def word22 {M : Type*} [Monoid M] (a b : M) : M := word21 a b * word07 a b
def word23 {M : Type*} [Monoid M] (a b : M) : M := word05 a b * word15 a b
def word24 {M : Type*} [Monoid M] (a b : M) : M := word15 a b * word05 a b
def word25 {M : Type*} [Monoid M] (a b : M) : M := word13 a b * word13 a b
def word26 {M : Type*} [Monoid M] (a b : M) : M := word23 a b * word24 a b
def word27 {M : Type*} [Monoid M] (a b : M) : M := word26 a b * word25 a b
def word28 {M : Type*} [Monoid M] (a b : M) : M := word16 a b * word17 a b
def word29 {M : Type*} [Monoid M] (a b : M) : M := word08 a b * word05 a b
def word30 {M : Type*} [Monoid M] (a b : M) : M := word03 a b * word14 a b
def word31 {M : Type*} [Monoid M] (a b : M) : M := word08 a b * word07 a b
def word32 {M : Type*} [Monoid M] (a b : M) : M := word28 a b * word29 a b
def word33 {M : Type*} [Monoid M] (a b : M) : M := word30 a b * word31 a b
def word34 {M : Type*} [Monoid M] (a b : M) : M := word32 a b * word33 a b
def word35 {M : Type*} [Monoid M] (a b : M) : M := word18 a b * word18 a b
def word36 {M : Type*} [Monoid M] (a b : M) : M := word06 a b * word06 a b
def word37 {M : Type*} [Monoid M] (a b : M) : M := word11 a b * word16 a b
def word38 {M : Type*} [Monoid M] (a b : M) : M := word03 a b * word11 a b
def word39 {M : Type*} [Monoid M] (a b : M) : M := word36 a b * word37 a b
def word40 {M : Type*} [Monoid M] (a b : M) : M := word39 a b * word38 a b
def word41 {M : Type*} [Monoid M] (a b : M) : M := word06 a b * word05 a b
def word42 {M : Type*} [Monoid M] (a b : M) : M := word05 a b * word09 a b
def word43 {M : Type*} [Monoid M] (a b : M) : M := word05 a b * word01 a b
def word44 {M : Type*} [Monoid M] (a b : M) : M := word17 a b * word03 a b
def word45 {M : Type*} [Monoid M] (a b : M) : M := word41 a b * word42 a b
def word46 {M : Type*} [Monoid M] (a b : M) : M := word43 a b * word44 a b
def word47 {M : Type*} [Monoid M] (a b : M) : M := word45 a b * word46 a b

theorem relation_7 {M : Type*} [Monoid M] (a b : M) :
    positiveRelation a b 7 = word22 a b := by
  change a * b * a * b * a * b ^ 2 * a * b ^ 4 * a * b ^ 3 * a * b ^ 4 * a * b ^ 2 * a * b * a * b * (a * b ^ 3) ^ 4 = word22 a b
  simp only [word00, word01, word02, word03, word04, word05, word06, word07, word08, word09, word10, word12, word13, word14, word19, word20, word21, word22, pow_succ, pow_zero, one_mul, mul_assoc]

theorem relation_8 {M : Type*} [Monoid M] (a b : M) :
    positiveRelation a b 8 = word27 a b := by
  change a * b * (a * b ^ 2 * (a * b ^ 3) ^ 2) ^ 2 * a * b ^ 2 * a * b * a * b ^ 2 * (a * b ^ 4 * a * b ^ 2) ^ 2 = word27 a b
  simp only [word00, word01, word02, word03, word04, word05, word07, word08, word10, word13, word15, word23, word24, word25, word26, word27, pow_succ, pow_zero, one_mul, mul_assoc]

theorem relation_9 {M : Type*} [Monoid M] (a b : M) :
    positiveRelation a b 9 = word34 a b := by
  change a * b * a * b * (a * b ^ 2) ^ 2 * a * b * (a * b ^ 4) ^ 2 * a * b * (a * b ^ 2) ^ 2 * a * b * a * b * a * b ^ 3 * a * b ^ 4 * a * b ^ 3 = word34 a b
  simp only [word00, word01, word02, word03, word04, word05, word06, word07, word08, word14, word16, word17, word28, word29, word30, word31, word32, word33, word34, pow_succ, pow_zero, one_mul, mul_assoc]

theorem relation_10 {M : Type*} [Monoid M] (a b : M) :
    positiveRelation a b 10 = word35 a b := by
  change (a * b * a * b * a * b ^ 2 * a * b ^ 4 * a * b ^ 3 * a * b * a * b * a * b ^ 4) ^ 2 = word35 a b
  simp only [word00, word01, word02, word03, word04, word05, word06, word07, word08, word09, word11, word12, word18, word35, pow_succ, pow_zero, one_mul, mul_assoc]

theorem relation_11 {M : Type*} [Monoid M] (a b : M) :
    positiveRelation a b 11 = word40 a b := by
  change (a * b * a * b * a * b ^ 2) ^ 2 * a * b * a * b * a * b ^ 4 * a * b * a * b * (a * b ^ 2) ^ 3 * a * b * a * b * a * b ^ 4 = word40 a b
  simp only [word00, word01, word02, word03, word04, word05, word06, word11, word16, word36, word37, word38, word39, word40, pow_succ, pow_zero, one_mul, mul_assoc]

theorem relation_12 {M : Type*} [Monoid M] (a b : M) :
    positiveRelation a b 12 = word47 a b := by
  change a * b * (a * b * a * b ^ 2) ^ 3 * a * b * a * b * a * b ^ 2 * a * b ^ 4 * a * b * a * b ^ 3 * a * b * a * b ^ 4 * a * b ^ 2 = word47 a b
  simp only [word00, word01, word02, word03, word04, word05, word06, word08, word09, word17, word41, word42, word43, word44, word45, word46, word47, pow_succ, pow_zero, one_mul, mul_assoc]

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords
