module
public import BenderGlauberman.ClassFunction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Data.ZMod.Basic
public import Theory.SpecificGroups.GL2.ThreeConjugacy

/-!
# The determinant-sign character of GL2(3)

The determinant map of the actual group GL(Fin 2)(ZMod 3), followed by
the sign embedding of the two field units into complex units, gives a
nontrivial linear irreducible character. Its value is one on determinant
one and minus one otherwise; its pointwise square is the trivial character.
The representative-values theorem evaluates it on the eight actual
conjugacy representatives in Wong’s column order.

The two field units are one and minus one, so their sign map is
multiplicative by a kernel-checked finite calculation. The existing linear
character constructor supplies an actual one-dimensional complex
representation and proves irreducibility. Determinant surjectivity proves
nontriviality. No characterhood is inferred from a proposed table.

This is the nontrivial degree-one row of W. J. Wong, On finite groups whose
2-Sylow subgroups have cyclic subgroups of index 2, Table 1, article p.97
(1964), and the determinant character used to twist its paired rows. It is
an independent prerequisite of the characteristic-three recognition route.
-/

namespace ABG
open Matrix.GeneralLinearGroup

private theorem unit_three_cases (u : (ZMod 3)ˣ) : u = 1 ∨ u = -1 := by
  revert u
  decide +kernel

private def unitThreeSign : (ZMod 3)ˣ →* ℂˣ where
  toFun u := if u = 1 then 1 else -1
  map_one' := by simp
  map_mul' u v := by
    have hne : (-1 : (ZMod 3)ˣ) ≠ 1 := by decide
    rcases unit_three_cases u with rfl | rfl <;>
      rcases unit_three_cases v with rfl | rfl <;> simp [hne]

public def glTwoThreeDeterminantSign : GL (Fin 2) (ZMod 3) →* ℂˣ :=
  unitThreeSign.comp det

public theorem glTwoThreeDeterminantSign_apply (A : GL (Fin 2) (ZMod 3)) :
    glTwoThreeDeterminantSign A = if det A = 1 then 1 else -1 := by rfl

@[expose] public def glTwoThreeDeterminantCharacter : ClassFunction (GL (Fin 2) (ZMod 3)) :=
  fun A => (glTwoThreeDeterminantSign A : ℂ)

public theorem glTwoThreeDeterminantCharacter_apply (A : GL (Fin 2) (ZMod 3)) :
    glTwoThreeDeterminantCharacter A = if det A = 1 then 1 else -1 := by
  by_cases h : det A = 1 <;>
    simp [glTwoThreeDeterminantCharacter, glTwoThreeDeterminantSign_apply, h]

public theorem glTwoThreeDeterminantCharacter_isLinear :
    IsLinearCharacter glTwoThreeDeterminantCharacter := by
  let : Fintype (GL (Fin 2) (ZMod 3)) := Fintype.ofFinite _
  exact BenderGlauberman.isLinearCharacter_of_hom glTwoThreeDeterminantSign

public theorem glTwoThreeDeterminantCharacter_ne_one :
    glTwoThreeDeterminantCharacter ≠ 1 := by
  obtain ⟨A, hA⟩ := det_surjective (n := Fin 2) (-1 : (ZMod 3)ˣ)
  intro heq
  have h := congrFun heq A
  rw [glTwoThreeDeterminantCharacter_apply, hA] at h
  have hne : (-1 : (ZMod 3)ˣ) ≠ 1 := by decide
  simp [hne] at h
  norm_num at h

public theorem glTwoThreeDeterminantCharacter_mul_self :
    glTwoThreeDeterminantCharacter * glTwoThreeDeterminantCharacter = 1 := by
  ext A
  change glTwoThreeDeterminantCharacter A * glTwoThreeDeterminantCharacter A = 1
  rw [glTwoThreeDeterminantCharacter_apply]
  split_ifs <;> norm_num

/-- The determinant-sign row on Wong's eight representatives. -/
public theorem glTwoThreeDeterminantCharacter_values (i : Fin 8) :
    glTwoThreeDeterminantCharacter (threeClassRepr i) = ![1,1,1,1,1,-1,-1,-1] i := by
  have hd : ∀ j : Fin 8, (det (threeClassRepr j) = 1) ↔ j.val < 5 := by
    decide +kernel
  rw [glTwoThreeDeterminantCharacter_apply]
  simp only [hd]
  fin_cases i <;> norm_num

end ABG
