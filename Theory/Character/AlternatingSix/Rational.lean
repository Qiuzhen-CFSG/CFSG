module

public import Theory.Character.AlternatingSix.Blocks
public import Theory.Character.AlternatingSix.Rational.Permutations
public import Theory.Character.AlternatingSix.Rational.NormOne
public import Theory.Character.AlternatingSix.Rational.Calculations
public import Theory.Character.AlternatingSix.Rational.ThreeClasses

/-!
# Rational characters of the alternating group on six letters

The point, pair and triple permutation characters give the virtual rows
`P₂-P₁`, `P₁²+1-2P₁-P₂`, `P₁-1`, and `P₃-P₂`.
Each is a difference of actual representation characters. Their positive
degrees and norm one therefore give actual irreducibles, by completeness.
The two degree-five rows are interchanged when the marked element of order
three has no fixed point in the natural action.

The checked finite row calculations and conjugacy separation in A6 discharge
both premises of the permutation construction. Thus `rationalBlock` and
`rationalBlock_nonempty` supply all four irreducibles and every prescribed
value for either order-three marking, assuming only `orderOf c = 3`.

Source: Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 6, pp.10–11, rows χ₂,χ₃,χ₆,χ₇.
-/

noncomputable section
namespace Theory.Character.AlternatingSix
open RationalConstruction

/-- The natural row order, interchanging the two degree-five rows exactly when
`c` is not a single three-cycle in the natural action. -/
@[expose] public def markedRowIndex (c : alternatingGroup (Fin 6)) (j : Fin 4) : Fin 4 :=
  if pointCount c = 3 then j else ![0, 1, 3, 2] j

private theorem marked_values_fixed (c : alternatingGroup (Fin 6)) (j : Fin 4)
    (r : Fin 6) (hr : r ≠ 2) (hs : r ≠ 3) :
    rationalValues (markedRowIndex c j) r = rationalValues j r := by
  unfold markedRowIndex
  split_ifs
  · rfl
  · fin_cases j <;> fin_cases r <;> simp_all [rationalValues]

private theorem marked_values_three (c : alternatingGroup (Fin 6)) (j : Fin 4) :
    rationalValues (markedRowIndex c j) (if pointCount c = 3 then 2 else 3) =
      rationalValues j 2 := by
  by_cases h : pointCount c = 3
  · simp [markedRowIndex, h]
  · fin_cases j <;> simp [markedRowIndex, h, rationalValues]

private theorem marked_values_other (c x : alternatingGroup (Fin 6)) (j : Fin 4)
    (h : pointCount x = 3 ↔ pointCount c ≠ 3) :
    rationalValues (markedRowIndex c j) (if pointCount x = 3 then 2 else 3) =
      rationalValues j 3 := by
  by_cases hc : pointCount c = 3
  · have hx : pointCount x ≠ 3 := fun hx => (h.mp hx) hc
    simp [markedRowIndex, hc, hx]
  · have hx : pointCount x = 3 := h.mpr hc
    fin_cases j <;> simp [markedRowIndex, hc, hx, rationalValues]

/-- Assemble the actual irreducible rational characters from finite permutation
calculations and separation of the two order-three classes. The premises refer
only to integer fixed-point counts and conjugacy, not to assumed characters. -/
public def rationalBlockOfPermutationCalculations (D : PermutationCalculations)
    (separation : OtherThreeSeparation) (c : alternatingGroup (Fin 6)) (hc : orderOf c = 3) :
    RationalBlock c where
  character j := rowCharacter (markedRowIndex c j)
  irreducible j := (rowCharacter_generalized _).irreducible_of_norm_one
    (by
      convert rowCharacter_norm_of_sum (markedRowIndex c j) (D.square_sum _) using 1
      exact congrArg (fun t : Fintype A6 => @scalarProduct A6 t
        (rowCharacter (markedRowIndex c j)) (rowCharacter (markedRowIndex c j)))
        (Subsingleton.elim _ _))
    (rowCharacter_degree_pos _)
  one j := by
    rw [rowCharacter_eq_values, rowValues_one, marked_values_fixed c j 0 (by decide) (by decide)]
  two j x hx := by
    rw [rowCharacter_eq_values, D.two _ x hx, marked_values_fixed c j 1 (by decide) (by decide)]
  three j := by
    rw [rowCharacter_eq_values, D.three _ c hc, marked_values_three]
  otherThree j x hx hxc := by
    rw [rowCharacter_eq_values, D.three _ x hx,
      marked_values_other c x j (separation c x hc hx hxc)]
  four j x hx := by
    rw [rowCharacter_eq_values, D.four _ x hx, marked_values_fixed c j 4 (by decide) (by decide)]
  five j x hx := by
    rw [rowCharacter_eq_values, D.five _ x hx, marked_values_fixed c j 5 (by decide) (by decide)]

/-- Conditional producer in the published `RationalBlock` interface. -/
public theorem rationalBlock_of_permutation_calculations (D : PermutationCalculations)
    (separation : OtherThreeSeparation) (c : alternatingGroup (Fin 6)) (hc : orderOf c = 3) :
    Nonempty (RationalBlock c) :=
  ⟨rationalBlockOfPermutationCalculations D separation c hc⟩

/-- The four actual rational irreducibles of A6, marked by any element of order
three. The finite counts, norm-one realization and A6 conjugacy separation are
all proved; no character or calculation premise remains. -/
public def rationalBlock (c : alternatingGroup (Fin 6)) (hc : orderOf c = 3) :
    RationalBlock c :=
  rationalBlockOfPermutationCalculations permutationCalculations otherThreeSeparation c hc

/-- Every order-three marking admits the rational rows of degrees `9,10,5,5`,
with all values required by the published `RationalBlock` interface. -/
public theorem rationalBlock_nonempty (c : alternatingGroup (Fin 6)) (hc : orderOf c = 3) :
    Nonempty (RationalBlock c) :=
  ⟨rationalBlock c hc⟩

end Theory.Character.AlternatingSix
