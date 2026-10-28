module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.RootGeometry
-- Internal split: reuse only the coordinate calculation in the preceding leaf.
import all Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.RootGeometry

/-!
# The exceptional action on the two marked A₂ systems

The explicit twelve-letter Weyl lift carries exceptional duality from the long
pair to the negatives of the short pair, and from the short pair to the long
pair. This is a calculation on actual root elements with arbitrary parameters.
It fixes the inverse-transpose convention of `SL3Pair`; opposition supplies
the further parity correction for arbitrary Ree parameters.
Source: GLS3 Example 2.6.3 and Table 4.7.3A.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction ReeF4.WordRelations
namespace ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem
open ReeF4.CentralCovers.OddPrimary.Cyclotomic
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem dual_rootWord (l : List (Fin 4)) (r : F4Chevalley.Root) :
    exceptionalRootPermutation (rootWord l r) =
      rootWord (l.map Fin.rev) (exceptionalRootPermutation r) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change exceptionalRootPermutation
      (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) (rootWord l r)) = _
    rw [exceptionalRootPermutation_simple_reflection, ih]
    rfl

private def lowestWord : List (Fin 4) := [0,1,2,3,1,2,1,0]

private theorem lowestWord_target : rootWord lowestWord (typeF4SimpleRootIndex 0) = longRoot false := by
  apply Subtype.ext
  ext q
  fin_cases q <;>
    norm_num [rootWord, lowestWord, reflectionWord, reflection_val,
      typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val,
      reflectedVector, typeF4SimpleRoot, longRoot,
      Three.Descent.ExceptionalTorus.lowestRoot, typeF4LowestRoot,
      Matrix.cons_val_two, Matrix.cons_val_three]

theorem twist_long_target (k : Bool) :
    rootWord twistWord (exceptionalRootPermutation (longRoot k)) = -shortRoot k := by
  cases k
  · rw [← lowestWord_target, dual_rootWord, exceptionalRootPermutation_simple]
    apply Subtype.ext
    rw [neg_val]
    ext q
    fin_cases q <;>
      norm_num [rootWord, twistWord, lowestWord, reflectionWord, reflection_val,
        typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val,
        reflectedVector, typeF4SimpleRoot, shortRoot,
        Matrix.cons_val_two, Matrix.cons_val_three, Fin.rev]
  · simp only [longRoot, ↓reduceIte, exceptionalRootPermutation_simple]
    apply Subtype.ext
    rw [neg_val]
    ext q
    fin_cases q <;>
      norm_num [rootWord, twistWord, reflectionWord, reflection_val,
        typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val,
        reflectedVector, typeF4SimpleRoot, shortRoot,
        Matrix.cons_val_two, Matrix.cons_val_three, Fin.rev]

theorem twist_short_target (k : Bool) :
    rootWord twistWord (exceptionalRootPermutation (shortRoot k)) = longRoot k := by
  cases k <;> simp only [shortRoot, Bool.false_eq_true, ↓reduceIte,
    exceptionalRootPermutation_simple]
  all_goals
    apply Subtype.ext
    ext q
    fin_cases q <;>
      norm_num [rootWord, twistWord, reflectionWord, reflection_val,
        typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val,
        reflectedVector, typeF4SimpleRoot, longRoot,
        Three.Descent.ExceptionalTorus.lowestRoot, typeF4LowestRoot,
        Matrix.cons_val_two, Matrix.cons_val_three, Fin.rev]

theorem signed_long (s k : Bool) : IsLongRoot (signedRoot s (longRoot k)) := by
  have h : IsLongRoot (longRoot k) := by
    cases k
    · exact Three.Descent.ExceptionalTorus.lowestRoot_long
    · exact (typeF4SimpleRootIndex_mem_pair_iff 0).mpr (by decide)
  cases s
  · exact (isLongRoot_neg_iff _).mpr h
  · exact h

theorem signed_short (s k : Bool) : IsShortRoot (signedRoot s (shortRoot k)) := by
  have h : IsShortRoot (shortRoot k) := by
    cases k
    · simpa only [shortRoot, Bool.false_eq_true, ↓reduceIte, IsShortRoot, IsLongRoot,
        typeF4SimpleRootIndex_mem_pair_iff] using (show ¬(3 : Fin 4).val < 2 by decide)
    · simpa only [shortRoot, ↓reduceIte, IsShortRoot, IsLongRoot,
        typeF4SimpleRootIndex_mem_pair_iff] using (show ¬(2 : Fin 4).val < 2 by decide)
  cases s
  · exact (isShortRoot_neg_iff _).mpr h
  · exact h

variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]

def opposition : AlgebraicPoints F := OppositeBorels.Maximality.opposition

theorem opposition_root (r : F4Chevalley.Root) (t : F) :
    opposition * rootPoint r t * opposition⁻¹ = rootPoint (-r) t :=
  OppositeBorels.Maximality.opposition_conj_root r t

theorem exceptional_rootPoint (r : F4Chevalley.Root) (t : F) :
    exceptionalPointEnd (rootPoint r t) =
      rootPoint (exceptionalRootPermutation r) (exceptionalParameter r t) :=
  ExceptionalMorphism.morphism_root r t

/-- The long factor has parameter exponent one and changes its root sign. -/
theorem baseTwist_long_root (s k : Bool) (t : F) :
    wordElement twistWord * exceptionalPointEnd (rootPoint (signedRoot s (longRoot k)) t) *
        (wordElement twistWord)⁻¹ = rootPoint (signedRoot (!s) (shortRoot k)) t := by
  rw [exceptional_rootPoint, exceptionalParameter_of_long (signed_long s k), wordElement_root]
  congr 1
  cases s <;>
    simp only [signedRoot, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true,
      exceptionalRootPermutation_neg, rootWord_neg, twist_long_target, neg_neg]

/-- The short factor has parameter exponent two and keeps its root sign. -/
theorem baseTwist_short_root (s k : Bool) (t : F) :
    wordElement twistWord * exceptionalPointEnd (rootPoint (signedRoot s (shortRoot k)) t) *
        (wordElement twistWord)⁻¹ = rootPoint (signedRoot s (longRoot k)) (t ^ 2) := by
  rw [exceptional_rootPoint, exceptionalParameter_of_short (signed_short s k), wordElement_root]
  congr 1
  cases s <;>
    simp only [signedRoot, Bool.false_eq_true, ↓reduceIte,
      exceptionalRootPermutation_neg, rootWord_neg, twist_short_target]

end ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem
