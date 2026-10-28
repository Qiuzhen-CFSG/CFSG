module

public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.RepresentativeCalculations.Elementary
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Affine.Generators.Word0
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Affine.Generators.Word1
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Affine.Generators.Word2
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Affine.Generators.Word3
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Affine.Generators.Word4
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Affine.Generators.Word5
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Affine.Generators.Word6
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Gen0
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Gen1
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Gen2
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Gen3
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Gen4
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Gen5
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Gen6
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Gen8
import Mathlib.Tactic.FinCases
/-!
# Checked basis actions of the fixed J₃ local generators

Each commuting square is checked on all 6156 permutation letters. The cached
permutations have already been proved equal to the original affine and Thompson
words; the elementary permutations use the identical affine chain words in
reverse order. Thus the checked squares certify genuine model conjugations.
The proposed masks come from `../source/finite-calculations.json`; the data and
its discovery program are not proof premises.

Source: GLS, Number 3, Table 5.3h, p.269, and the retained ATLAS J3G1-p6156B0
model. No ambient normalizer or transitivity assertion is assumed here.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.RepresentativeCalculations.LocalActions
open Subgroup Sporadic.Janko3 Sporadic.Janko3.TwoLocal Theory.GroupTheory
open Sporadic.Janko3.OrderCertificate Sporadic.Janko3.TwoLocal.AffineCertificate
open Sporadic.Janko3.TwoLocal.ThompsonCertificate
set_option Elab.async false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

@[expose] public def fastAffine : Fin 7 → Equiv.Perm (Fin 6156) := ![G0, G1, G2, G3, G4, G5, G6]
@[expose] public def fastElementary : Fin 4 → Equiv.Perm (Fin 6156) := ![G3, G2, G1, G0]
@[expose] public def fastElement (i : Fin 16) : Equiv.Perm (Fin 6156) :=
  evalWord fastElementary (elementaryWord i)


public theorem fastAffine_eq (i : Fin 7) : fastAffine i = embedding (affineGenerator i) := by
  fin_cases i
  · exact G0_eq
  · exact G1_eq
  · exact G2_eq
  · exact G3_eq
  · exact G4_eq
  · exact G5_eq
  · exact G6_eq

public theorem fastElementary_eq (i : Fin 4) :
    fastElementary i = embedding (elementaryGenerator i) := by
  fin_cases i
  · exact G3_eq
  · exact G2_eq
  · exact G1_eq
  · exact G0_eq

public theorem fastElement_eq (i : Fin 16) :
    fastElement i = embedding (elementaryElement i) := by
  have hw (w : List (Fin 4)) : evalWord fastElementary w =
      embedding (evalWord elementaryGenerator w) := by
    induction w with
    | nil => exact (map_one embedding).symm
    | cons j w ih => simp only [evalWord, map_mul, ← fastElementary_eq, ← ih]
  exact hw _

@[expose] public def fastThompson : Fin 8 → Equiv.Perm (Fin 6156) :=
  ![(g1 : Equiv.Perm (Fin 6156)), g5, g4, g3, g2, g0, g8, g6]

public theorem fastThompson_eq (i : Fin 8) :
    fastThompson i = embedding (thompsonNormalizerGenerator i) := by
  fin_cases i
  · exact congrArg Subtype.val g1_eq
  · exact congrArg Subtype.val g5_eq
  · exact congrArg Subtype.val g4_eq
  · exact congrArg Subtype.val g3_eq
  · exact congrArg Subtype.val g2_eq
  · exact congrArg Subtype.val g0_eq
  · exact congrArg Subtype.val g8_eq
  · exact congrArg Subtype.val g6_eq

/-- Equality on every permutation letter certifies a model conjugation. -/
public theorem image_of_square (g : Model) (p : Equiv.Perm (Fin 6156))
    (hp : p = embedding g) (j : Fin 4) (i : Fin 16)
    (h : ∀ x : Fin 6156, p (fastElementary j x) = fastElement i (p x)) :
    (MulAut.conj g) (elementaryGenerator j) = elementaryElement i := by
  rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change embedding (g * elementaryGenerator j) = embedding (elementaryElement i * g)
  simp only [map_mul, ← hp, ← fastElementary_eq, ← fastElement_eq]
  exact Equiv.ext h

@[expose] public def affineBasisImage : Fin 7 → Fin 4 → Fin 16 :=
  ![![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![1, 2, 4, 8], ![6, 5, 11, 15], ![2, 5, 14, 10], ![14, 11, 12, 10]]

@[expose] public def thompsonBasisImage : Fin 8 → Fin 4 → Fin 16 :=
  ![![1, 0, 4, 0], ![1, 0, 4, 0], ![1, 0, 4, 0], ![1, 0, 4, 0], ![1, 0, 4, 0], ![1, 0, 4, 0], ![1, 0, 5, 0], ![5, 0, 1, 0]]

private theorem affine_square_0 (j : Fin 4) : ∀ x : Fin 6156,
    fastAffine 0 (fastElementary j x) =
      fastElement (affineBasisImage 0 j) (fastAffine 0 x) := by
  fin_cases j <;> apply allLetters <;> decide +kernel

private theorem affine_square_1 (j : Fin 4) : ∀ x : Fin 6156,
    fastAffine 1 (fastElementary j x) =
      fastElement (affineBasisImage 1 j) (fastAffine 1 x) := by
  fin_cases j <;> apply allLetters <;> decide +kernel

private theorem affine_square_2 (j : Fin 4) : ∀ x : Fin 6156,
    fastAffine 2 (fastElementary j x) =
      fastElement (affineBasisImage 2 j) (fastAffine 2 x) := by
  fin_cases j <;> apply allLetters <;> decide +kernel

private theorem affine_square_3 (j : Fin 4) : ∀ x : Fin 6156,
    fastAffine 3 (fastElementary j x) =
      fastElement (affineBasisImage 3 j) (fastAffine 3 x) := by
  fin_cases j <;> apply allLetters <;> decide +kernel

private theorem affine_square_4 (j : Fin 4) : ∀ x : Fin 6156,
    fastAffine 4 (fastElementary j x) =
      fastElement (affineBasisImage 4 j) (fastAffine 4 x) := by
  fin_cases j <;> apply allLetters <;> decide +kernel

private theorem affine_square_5 (j : Fin 4) : ∀ x : Fin 6156,
    fastAffine 5 (fastElementary j x) =
      fastElement (affineBasisImage 5 j) (fastAffine 5 x) := by
  fin_cases j <;> apply allLetters <;> decide +kernel

private theorem affine_square_6 (j : Fin 4) : ∀ x : Fin 6156,
    fastAffine 6 (fastElementary j x) =
      fastElement (affineBasisImage 6 j) (fastAffine 6 x) := by
  fin_cases j <;> apply allLetters <;> decide +kernel

public theorem affine_basis_image (k : Fin 7) (j : Fin 4) :
    (MulAut.conj (affineGenerator k)) (elementaryGenerator j) =
      elementaryElement (affineBasisImage k j) := by
  apply image_of_square _ _ (fastAffine_eq k)
  fin_cases k
  · exact affine_square_0 j
  · exact affine_square_1 j
  · exact affine_square_2 j
  · exact affine_square_3 j
  · exact affine_square_4 j
  · exact affine_square_5 j
  · exact affine_square_6 j

private theorem thompson_square_0 (j : Fin 4)
    (hj : (5 : Nat).testBit j.val = true) : ∀ x : Fin 6156,
    fastThompson 0 (fastElementary j x) =
      fastElement (thompsonBasisImage 0 j) (fastThompson 0 x) := by
  fin_cases j
  · apply allLetters; decide +kernel
  · contradiction
  · apply allLetters; decide +kernel
  · contradiction

private theorem thompson_square_1 (j : Fin 4)
    (hj : (5 : Nat).testBit j.val = true) : ∀ x : Fin 6156,
    fastThompson 1 (fastElementary j x) =
      fastElement (thompsonBasisImage 1 j) (fastThompson 1 x) := by
  fin_cases j
  · apply allLetters; decide +kernel
  · contradiction
  · apply allLetters; decide +kernel
  · contradiction

private theorem thompson_square_2 (j : Fin 4)
    (hj : (5 : Nat).testBit j.val = true) : ∀ x : Fin 6156,
    fastThompson 2 (fastElementary j x) =
      fastElement (thompsonBasisImage 2 j) (fastThompson 2 x) := by
  fin_cases j
  · apply allLetters; decide +kernel
  · contradiction
  · apply allLetters; decide +kernel
  · contradiction

private theorem thompson_square_3 (j : Fin 4)
    (hj : (5 : Nat).testBit j.val = true) : ∀ x : Fin 6156,
    fastThompson 3 (fastElementary j x) =
      fastElement (thompsonBasisImage 3 j) (fastThompson 3 x) := by
  fin_cases j
  · apply allLetters; decide +kernel
  · contradiction
  · apply allLetters; decide +kernel
  · contradiction

private theorem thompson_square_4 (j : Fin 4)
    (hj : (5 : Nat).testBit j.val = true) : ∀ x : Fin 6156,
    fastThompson 4 (fastElementary j x) =
      fastElement (thompsonBasisImage 4 j) (fastThompson 4 x) := by
  fin_cases j
  · apply allLetters; decide +kernel
  · contradiction
  · apply allLetters; decide +kernel
  · contradiction

private theorem thompson_square_5 (j : Fin 4)
    (hj : (5 : Nat).testBit j.val = true) : ∀ x : Fin 6156,
    fastThompson 5 (fastElementary j x) =
      fastElement (thompsonBasisImage 5 j) (fastThompson 5 x) := by
  fin_cases j
  · apply allLetters; decide +kernel
  · contradiction
  · apply allLetters; decide +kernel
  · contradiction

private theorem thompson_square_6 (j : Fin 4)
    (hj : (5 : Nat).testBit j.val = true) : ∀ x : Fin 6156,
    fastThompson 6 (fastElementary j x) =
      fastElement (thompsonBasisImage 6 j) (fastThompson 6 x) := by
  fin_cases j
  · apply allLetters; decide +kernel
  · contradiction
  · apply allLetters; decide +kernel
  · contradiction

private theorem thompson_square_7 (j : Fin 4)
    (hj : (5 : Nat).testBit j.val = true) : ∀ x : Fin 6156,
    fastThompson 7 (fastElementary j x) =
      fastElement (thompsonBasisImage 7 j) (fastThompson 7 x) := by
  fin_cases j
  · apply allLetters; decide +kernel
  · contradiction
  · apply allLetters; decide +kernel
  · contradiction

public theorem thompson_basis_image (k : Fin 8) (j : Fin 4)
    (hj : (5 : Nat).testBit j.val = true) :
    (MulAut.conj (thompsonNormalizerGenerator k)) (elementaryGenerator j) =
      elementaryElement (thompsonBasisImage k j) := by
  apply image_of_square _ _ (fastThompson_eq k)
  fin_cases k
  · exact thompson_square_0 j hj
  · exact thompson_square_1 j hj
  · exact thompson_square_2 j hj
  · exact thompson_square_3 j hj
  · exact thompson_square_4 j hj
  · exact thompson_square_5 j hj
  · exact thompson_square_6 j hj
  · exact thompson_square_7 j hj

end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.RepresentativeCalculations.LocalActions
