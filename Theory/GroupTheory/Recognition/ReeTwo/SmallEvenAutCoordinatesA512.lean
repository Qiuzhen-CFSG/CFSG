module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenCandidates
public import Theory.SpecificGroups.ReeTwo.SmallEvenAutProfilesA
public import Theory.SpecificGroups.ReeTwo.EvenCoordinates

/-!
# Coordinates for the six order-512 small even candidates

The five rank-four rows use generator positions [1,2,3,6], [1,2,3,5],
[1,2,3,4], [1,2,3,4], and [1,2,3,6] for candidates 0,1,2,5,6.
Candidate 4 has rank three with positions [1,2,3]. The coordinates below
use this exact basis convention. Explicit words in these lifts provide
sections on the original generator closures. Candidate 4 requires a quadratic
correction in its third coordinate.

Source: Shinoda (1975), (2.3), pp. 81–82, through the verified root model
in `Core`, `RootAction`, and `Sylow`; the profile convention is documented
in `SmallEvenAutProfilesA`. All section identities are kernel checked.
-/

namespace ReeTwo.SylowModel
open ReeTwo.SmallEvenAutProfilesA
set_option maxRecDepth 16384

/-- The rank-four profile row associated to one of the five order-512 cases. -/
@[expose] public def smallEvenFourRowA512 (j : Fin 5) : Fin 16 := j.castLE (by decide)

/-- The six candidate indices, with the rank-three case in position three. -/
@[expose] public def smallEvenIndexA512 : Fin 6 → Fin 59 := ![0,1,2,4,5,6]

/-- The original nine displayed generators, in their original order. -/
@[expose] public def smallEvenGeneratorsA512 (i : Fin 6) : Fin 9 → SylowModel :=
  (![![rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9],
    ![rootOne ^ 2 * root 0 * root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3 * root 4 * root 7 * root 8, rootOne ^ 2, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9],
    ![root 0, rootOne ^ 2 * root 0 * root 3, root 4 * root 7 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 9, root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 8 * root 9, root 9],
    ![root 0 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, rootOne ^ 2 * root 0 * root 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9],
    ![root 3, rootOne ^ 2 * root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, root 2 * root 3 * root 4 * root 7, root 4 * root 7 * root 8, root 6, root 7 * root 8, root 8 * root 9, root 9],
    ![root 3, rootOne ^ 2, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, root 5 * root 8, root 4 * root 7 * root 8 * root 9, root 6 * root 8, root 7 * root 8 * root 9, root 8, root 9]]) i

/-- Each of the nine words belongs to the corresponding original closure. -/
public theorem smallEvenGeneratorsA512_mem (i : Fin 6) (k : Fin 9) :
    smallEvenGeneratorsA512 i k ∈ smallEvenCandidate (smallEvenIndexA512 i) := by
  fin_cases i <;> fin_cases k <;> apply Subgroup.subset_closure
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))

/-- The four quotient coordinates, read on the ambient Sylow model. -/
@[expose] public def smallEvenFourCoordinatesA512 (j : Fin 5) (x : SylowModel) :
    FourQuotient :=
  let b := x.left
  let t : ZMod 2 := (x.right.toAdd.val / 2 : ℕ)
  Multiplicative.ofAdd
    (![![b.b0 + b.b3 + b.b4, b.b3 + b.b4, b.b0 + t, b.b5 + b.b6],
      ![b.b0 + b.b2 + b.b4, b.b2 + b.b4, b.b0 + t, b.b2 + b.b6],
      ![b.b0 + t, t, b.b3 + b.b4 + t, b.b5 + t],
      ![b.b2 + b.b3 + t, t, b.b2 + b.b4 + b.b5, b.b4 + b.b5],
      ![b.b1 + b.b3, t, b.b1, b.b1 + b.b6]]) j

/-- Candidate 4's rank-three coordinates, including the quadratic correction. -/
@[expose] public def smallEvenThreeCoordinatesA512 (x : SylowModel) : ThreeQuotient :=
  let b := x.left
  let t : ZMod 2 := (x.right.toAdd.val / 2 : ℕ)
  Multiplicative.ofAdd ![b.b2 + b.b3 + t, t, b.b4 + b.b5 + b.b1 * b.b3 + b.b1 * t + b.b2 * b.b3 + b.b3 * t]

/-- The ordered basis lifts for the five rank-four profiles. -/
@[expose] public def smallEvenFourBasisA512 (j : Fin 5) : Fin 4 → SylowModel :=
  (![![smallEvenGeneratorsA512 0 0, smallEvenGeneratorsA512 0 1, smallEvenGeneratorsA512 0 2, smallEvenGeneratorsA512 0 5],
    ![smallEvenGeneratorsA512 1 0, smallEvenGeneratorsA512 1 1, smallEvenGeneratorsA512 1 2, smallEvenGeneratorsA512 1 4],
    ![smallEvenGeneratorsA512 2 0, smallEvenGeneratorsA512 2 1, smallEvenGeneratorsA512 2 2, smallEvenGeneratorsA512 2 3],
    ![smallEvenGeneratorsA512 4 0, smallEvenGeneratorsA512 4 1, smallEvenGeneratorsA512 4 2, smallEvenGeneratorsA512 4 3],
    ![smallEvenGeneratorsA512 5 0, smallEvenGeneratorsA512 5 1, smallEvenGeneratorsA512 5 2, smallEvenGeneratorsA512 5 5]]) j

/-- Candidate 4's three ordered basis lifts. -/
@[expose] public def smallEvenThreeBasisA512 (k : Fin 3) : SylowModel :=
  smallEvenGeneratorsA512 3 (k.castLE (by decide))

public theorem smallEvenFourBasisA512_mem (j : Fin 5) (k : Fin 4) :
    smallEvenFourBasisA512 j k ∈ smallEvenCandidate (fourIndex (smallEvenFourRowA512 j)) := by
  fin_cases j <;> fin_cases k <;> apply Subgroup.subset_closure
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

public theorem smallEvenThreeBasisA512_mem (k : Fin 3) :
    smallEvenThreeBasisA512 k ∈ smallEvenCandidate 4 := by
  fin_cases k <;> apply Subgroup.subset_closure
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))

/-- An ambient word for each rank-four quotient value. -/
@[expose] public def smallEvenFourSectionA512 (j : Fin 5) (v : FourQuotient) : SylowModel :=
  smallEvenFourBasisA512 j 0 ^ (v.toAdd 0).val *
    smallEvenFourBasisA512 j 1 ^ (v.toAdd 1).val *
    smallEvenFourBasisA512 j 2 ^ (v.toAdd 2).val *
    smallEvenFourBasisA512 j 3 ^ (v.toAdd 3).val

/-- An ambient word for each rank-three quotient value. -/
@[expose] public def smallEvenThreeSectionA512 (v : ThreeQuotient) : SylowModel :=
  smallEvenThreeBasisA512 0 ^ (v.toAdd 0).val *
    smallEvenThreeBasisA512 1 ^ (v.toAdd 1).val *
    smallEvenThreeBasisA512 2 ^ (v.toAdd 2).val

public theorem smallEvenFourSectionA512_mem (j : Fin 5) (v : FourQuotient) :
    smallEvenFourSectionA512 j v ∈ smallEvenCandidate (fourIndex (smallEvenFourRowA512 j)) := by
  unfold smallEvenFourSectionA512
  repeat apply Subgroup.mul_mem
  all_goals exact Subgroup.pow_mem _ (smallEvenFourBasisA512_mem j _) _

public theorem smallEvenThreeSectionA512_mem (v : ThreeQuotient) :
    smallEvenThreeSectionA512 v ∈ smallEvenCandidate 4 := by
  unfold smallEvenThreeSectionA512
  repeat apply Subgroup.mul_mem
  all_goals exact Subgroup.pow_mem _ (smallEvenThreeBasisA512_mem _) _

private def fourBasisData (j : Fin 5) : Fin 4 → ZMod 2 × Core :=
  (![![(1, ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩), (1, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩), (1, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩), (0, ⟨0, 0, 0, 0, 0, 0, 1, 1, 1, 1⟩)],
    ![(1, ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩), (1, ⟨1, 0, 1, 0, 0, 1, 1, 0, 0, 1⟩), (1, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩), (0, ⟨0, 0, 1, 1, 1, 0, 0, 0, 0, 1⟩)],
    ![(0, ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩), (1, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩), (0, ⟨0, 0, 0, 0, 1, 0, 0, 1, 1, 0⟩), (0, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩)],
    ![(0, ⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩), (1, ⟨0, 1, 0, 1, 1, 1, 1, 0, 1, 1⟩), (0, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩), (0, ⟨0, 0, 1, 1, 1, 0, 0, 1, 0, 0⟩)],
    ![(0, ⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩), (1, ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩), (0, ⟨0, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩), (0, ⟨0, 0, 0, 0, 0, 0, 1, 0, 1, 0⟩)]]) j

private def threeBasisData : Fin 3 → ZMod 2 × Core :=
  ![(0, ⟨1, 1, 0, 1, 0, 1, 1, 1, 0, 1⟩), (1, ⟨1, 0, 1, 0, 1, 1, 1, 1, 1, 0⟩), (0, ⟨0, 0, 1, 1, 1, 1, 1, 1, 0, 1⟩)]

private theorem fourBasis_eq_data : ∀ j k,
    smallEvenFourBasisA512 j k = evenElement (fourBasisData j k).1 (fourBasisData j k).2 := by
  decide +kernel

private theorem threeBasis_eq_data : ∀ k,
    smallEvenThreeBasisA512 k = evenElement (threeBasisData k).1 (threeBasisData k).2 := by
  decide +kernel

private theorem evenElement_pow_bit (t : ZMod 2) (b : Core) (z : ZMod 2) :
    evenElement t b ^ z.val = evenElement (if z = 0 then 0 else t)
      (if z = 0 then 1 else b) := by
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) z with rfl | rfl
  · exact pow_zero _
  · exact pow_one _

/-- The rank-four section realizes every label in the profile convention. -/
public theorem smallEvenFourCoordinatesA512_section : ∀ j v,
    smallEvenFourCoordinatesA512 j (smallEvenFourSectionA512 j v) = v := by
  intro j v
  simp only [smallEvenFourSectionA512, fourBasis_eq_data, evenElement_pow_bit, evenElement_mul]
  revert j v
  decide +kernel

/-- The rank-three section realizes every label in the profile convention. -/
public theorem smallEvenThreeCoordinatesA512_section : ∀ v,
    smallEvenThreeCoordinatesA512 (smallEvenThreeSectionA512 v) = v := by
  intro v
  simp only [smallEvenThreeSectionA512, threeBasis_eq_data, evenElement_pow_bit, evenElement_mul]
  revert v
  decide +kernel

/-- The rank-four coordinate function on the original subgroup. -/
@[expose] public def smallEvenFourMapA512 (j : Fin 5)
    (x : smallEvenCandidate (fourIndex (smallEvenFourRowA512 j))) : FourQuotient :=
  smallEvenFourCoordinatesA512 j x.val

/-- The rank-three coordinate function on the original subgroup. -/
@[expose] public def smallEvenThreeMapA512 (x : smallEvenCandidate 4) : ThreeQuotient :=
  smallEvenThreeCoordinatesA512 x.val

public theorem smallEvenFourMapA512_surjective (j : Fin 5) :
    Function.Surjective (smallEvenFourMapA512 j) := fun v =>
  ⟨⟨smallEvenFourSectionA512 j v, smallEvenFourSectionA512_mem j v⟩,
    smallEvenFourCoordinatesA512_section j v⟩

public theorem smallEvenThreeMapA512_surjective :
    Function.Surjective smallEvenThreeMapA512 := fun v =>
  ⟨⟨smallEvenThreeSectionA512 v, smallEvenThreeSectionA512_mem v⟩,
    smallEvenThreeCoordinatesA512_section v⟩

/-- Coordinate equations for the six proposed carriers. Equality with the original
closures is a separate certificate. -/
@[expose] public def smallEvenCarrierA512 (i : Fin 6) (x : SylowModel) : Prop :=
  let b := x.left
  let t : ZMod 2 := (x.right.toAdd.val / 2 : ℕ)
  parity x.right = 1 ∧
    (![b.b1 = 0 ∧ b.b4 = b.b2,
      b.b1 = 0 ∧ b.b4 = b.b3,
      b.b1 = 0 ∧ b.b3 = b.b2 + t,
      b.b0 = b.b1 + t ∧ b.b3 = b.b1 + t + b.b2,
      b.b0 = 0 ∧ b.b1 = t,
      b.b0 = 0 ∧ b.b2 = 0]) i

/-- Nine independent bits satisfying the indicated carrier equations. -/
@[expose] public def smallEvenElementA512 (i : Fin 6) (w : Fin 9 → ZMod 2) : SylowModel :=
  ⟨(![(⟨w 0, 0, w 1, w 2, w 1, w 3, w 4, w 5, w 6, w 7⟩ : Core),
      ⟨w 0, 0, w 1, w 2, w 2, w 3, w 4, w 5, w 6, w 7⟩,
      ⟨w 0, 0, w 1, w 1 + w 8, w 2, w 3, w 4, w 5, w 6, w 7⟩,
      ⟨w 0 + w 8, w 0, w 1, w 0 + w 8 + w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩,
      ⟨0, w 8, w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩,
      ⟨0, w 0, 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩]) i,
    Multiplicative.ofAdd (2 * (w 8).val)⟩

/-- The nine free coordinates, in the order used by `smallEvenElementA512`. -/
@[expose] public def smallEvenParametersA512 (i : Fin 6) (x : SylowModel) : Fin 9 → ZMod 2 :=
  let b := x.left
  let t : ZMod 2 := (x.right.toAdd.val / 2 : ℕ)
  (![![b.b0, b.b2, b.b3, b.b5, b.b6, b.b7, b.b8, b.b9, t],
      ![b.b0, b.b2, b.b3, b.b5, b.b6, b.b7, b.b8, b.b9, t],
      ![b.b0, b.b2, b.b4, b.b5, b.b6, b.b7, b.b8, b.b9, t],
      ![b.b1, b.b2, b.b4, b.b5, b.b6, b.b7, b.b8, b.b9, t],
      ![b.b2, b.b3, b.b4, b.b5, b.b6, b.b7, b.b8, b.b9, t],
      ![b.b1, b.b3, b.b4, b.b5, b.b6, b.b7, b.b8, b.b9, t]]) i

private theorem highBit_twice (t : ZMod 2) :
    (((2 * t.val : ZMod 4).val / 2 : ℕ) : ZMod 2) = t :=
  (by decide : ∀ t : ZMod 2, (((2 * t.val : ZMod 4).val / 2 : ℕ) : ZMod 2) = t) t

/-- Reading the nine free coordinates recovers the parameters exactly. -/
public theorem smallEvenParametersA512_element (i : Fin 6) (w : Fin 9 → ZMod 2) :
    smallEvenParametersA512 i (smallEvenElementA512 i w) = w := by
  funext k
  fin_cases i <;> fin_cases k
  all_goals first | rfl | exact highBit_twice _

/-- Every parametrized point satisfies the carrier equations. -/
public theorem smallEvenElementA512_carrier (i : Fin 6) (w : Fin 9 → ZMod 2) :
    smallEvenCarrierA512 i (smallEvenElementA512 i w) := by
  have hp : parity (Multiplicative.ofAdd (2 * (w 8).val)) = 1 :=
    (by decide : ∀ t : ZMod 2, parity (Multiplicative.ofAdd (2 * t.val)) = 1) _
  fin_cases i
  · exact ⟨hp, rfl, rfl⟩
  · exact ⟨hp, rfl, rfl⟩
  · exact ⟨hp, rfl, congrArg (w 1 + ·) (highBit_twice (w 8)).symm⟩
  · exact ⟨hp, congrArg (w 0 + ·) (highBit_twice (w 8)).symm,
      congrArg (fun t => w 0 + t + w 1) (highBit_twice (w 8)).symm⟩
  · exact ⟨hp, rfl, (highBit_twice (w 8)).symm⟩
  · exact ⟨hp, rfl, rfl⟩

/-- The carrier equations reconstruct the dependent coordinates. -/
public theorem smallEvenElementA512_parameters (i : Fin 6) (x : SylowModel)
    (hx : smallEvenCarrierA512 i x) :
    smallEvenElementA512 i (smallEvenParametersA512 i x) = x := by
  have hr : Multiplicative.ofAdd (2 * ((((x.right.toAdd.val / 2 : ℕ) : ZMod 2).val) : ZMod 4)) =
      x.right := (by decide : ∀ t : FiveFour.Cyclic 4, parity t = 1 →
        Multiplicative.ofAdd (2 * ((((t.toAdd.val / 2 : ℕ) : ZMod 2).val) : ZMod 4)) = t)
      x.right hx.1
  apply SemidirectProduct.ext
  · fin_cases i <;> obtain ⟨_, h₁, h₂⟩ := hx
    all_goals apply Core.ext
    all_goals first | rfl | exact h₁.symm | exact h₂.symm
  · fin_cases i <;> exact hr

/-- A genuine equivalence for the equation-defined carrier, before identifying its closure. -/
@[expose] public def smallEvenCarrierEquivA512 (i : Fin 6) :
    (Fin 9 → ZMod 2) ≃ {x : SylowModel // smallEvenCarrierA512 i x} where
  toFun w := ⟨smallEvenElementA512 i w, smallEvenElementA512_carrier i w⟩
  invFun x := smallEvenParametersA512 i x.val
  left_inv := smallEvenParametersA512_element i
  right_inv x := Subtype.ext (smallEvenElementA512_parameters i x.val x.property)

/-- Each equation-defined carrier has 512 elements. -/
public theorem smallEvenCarrierA512_card (i : Fin 6) :
    Nat.card {x : SylowModel // smallEvenCarrierA512 i x} = 512 := by
  rw [Nat.card_congr (smallEvenCarrierEquivA512 i).symm, Nat.card_fun]
  simp

/-- Intrinsic fiber counts for the fixed rank-four coordinate functions. -/
@[expose] public noncomputable def smallEvenFourCoordinateProfileA512 (j : Fin 5)
    (v : FourQuotient) : ℕ × ℕ :=
  (Nat.card {x : smallEvenCandidate (fourIndex (smallEvenFourRowA512 j)) //
      smallEvenFourMapA512 j x = v ∧
        MulAut.orderCentralizerTest (fourTests (smallEvenFourRowA512 j) 0) x},
    Nat.card {x : smallEvenCandidate (fourIndex (smallEvenFourRowA512 j)) //
      smallEvenFourMapA512 j x = v ∧
        MulAut.orderCentralizerTest (fourTests (smallEvenFourRowA512 j) 1) x})

/-- Intrinsic fiber counts for the fixed rank-three coordinate function. -/
@[expose] public noncomputable def smallEvenThreeCoordinateProfileA512 (v : ThreeQuotient) : ℕ :=
  Nat.card {x : smallEvenCandidate 4 // smallEvenThreeMapA512 x = v ∧
    MulAut.orderCentralizerTest threeTest x}

end ReeTwo.SylowModel
