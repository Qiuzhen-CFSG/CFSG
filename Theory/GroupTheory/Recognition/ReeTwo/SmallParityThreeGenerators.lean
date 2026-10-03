module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityProfiles

/-!
# Ordered generators for the six rank-three parity candidates

The generators below are exactly the root words defining the six subgroups in
`SmallParityRepresentatives`, with repeated final generators padding each row
to length nine. Their closure is proved equal to the original subgroup, so
coordinate models may use this finite indexed family without changing the
group being studied. The three selected lifts retain the basis order used by
`SmallParityThreeProfile`; no independence or quotient assertion is made here.

Source: Shinoda (1975), (2.3), pp. 81–82, as realized by `ReeTwo.Sylow`.
The row labels are 76, 209, 458, 459, 460, and 478.
-/

namespace ReeTwo.SylowModel

private theorem repeat_last {α : Type*} (x : α) : insert x ({x} : Set α) = {x} :=
  Set.insert_eq_of_mem rfl

/-- Ordered defining generators, padded by repeating the final generator. -/
@[expose] public def smallParityThreeGenerator (i : Fin 6) : Fin 9 → SylowModel :=
  (![![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9,
      rootOne * root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 8 * root 9,
      rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9,
      root 4 * root 6 * root 7, root 4 * root 5 * root 7 * root 9,
      root 6 * root 7, root 7 * root 9, root 8, root 9],
    ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9,
      rootOne * root 0 * root 1 * root 2 * root 3 * root 7 * root 8 * root 9,
      rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9,
      root 6, root 4 * root 5 * root 7 * root 9, root 7 * root 8,
      root 8 * root 9, root 9, root 9],
    ![root 3 * root 6 * root 7 * root 8, rootOne ^ 3, rootOne ^ 2, root 4,
      root 7 * root 8 * root 9, root 9, root 8, root 8, root 8],
    ![root 3, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8,
      root 4 * root 9, root 7 * root 8 * root 9, root 9, root 8, root 8, root 8],
    ![root 3 * root 6 * root 7 * root 8, rootOne ^ 3 * root 5 * root 8,
      rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9,
      root 7 * root 8 * root 9, root 9, root 8, root 8, root 8],
    ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9,
      rootOne * root 0 * root 1 * root 2 * root 3 * root 6 * root 7 * root 8 * root 9,
      rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9,
      root 7 * root 9, root 4 * root 5 * root 7 * root 9, root 8 * root 9,
      root 9, root 9, root 9]]) i

/-- The indexed root words generate the exact subgroup in the original family. -/
public theorem smallParityThreeCandidate_eq_closure (i : Fin 6) :
    smallParityTwoCandidate (smallParityThreeIndex i) =
      Subgroup.closure (Set.range (smallParityThreeGenerator i)) := by
  unfold smallParityTwoCandidate
  apply congrArg Subgroup.closure
  fin_cases i <;>
    simp only [smallParityThreeIndex, smallParityThreeGenerator,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val, Matrix.range_cons,
      Matrix.range_empty, Set.singleton_union, Set.union_empty,
      repeat_last]

/-- Each indexed root word belongs to the intended candidate. -/
public theorem smallParityThreeGenerator_mem (i : Fin 6) (j : Fin 9) :
    smallParityThreeGenerator i j ∈ smallParityTwoCandidate (smallParityThreeIndex i) := by
  rw [smallParityThreeCandidate_eq_closure]
  exact Subgroup.subset_closure (Set.mem_range_self j)

/-- Defining generators as elements of the exact subgroup type. -/
@[expose] public def smallParityThreeGeneratorLift (i : Fin 6) (j : Fin 9) :
    smallParityTwoCandidate (smallParityThreeIndex i) :=
  ⟨smallParityThreeGenerator i j, smallParityThreeGenerator_mem i j⟩

/-- The lifted family generates the subgroup as an abstract group. -/
public theorem smallParityThreeGeneratorLift_closure (i : Fin 6) :
    Subgroup.closure (Set.range (smallParityThreeGeneratorLift i)) = ⊤ := by
  let K := Subgroup.closure (Set.range (smallParityThreeGeneratorLift i))
  have hle : smallParityTwoCandidate (smallParityThreeIndex i) ≤
      K.map (smallParityTwoCandidate (smallParityThreeIndex i)).subtype := by
    conv_lhs => rw [smallParityThreeCandidate_eq_closure]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    exact Subgroup.mem_map.mpr ⟨smallParityThreeGeneratorLift i j,
      Subgroup.subset_closure (Set.mem_range_self j), rfl⟩
  apply top_unique
  intro x _
  obtain ⟨y, hy, he⟩ := Subgroup.mem_map.mp (hle x.property)
  exact (show y = x from Subtype.ext he) ▸ hy

/-- Zero-based generator positions of the three proposed quotient basis lifts. -/
@[expose] public def smallParityThreeBasisPosition (i : Fin 6) : Fin 3 → Fin 9 :=
  ![0, 1, if i = 3 then 4 else 3]

/-- The three lifts in the profile's least-significant-bit-first convention. -/
@[expose] public def smallParityThreeBasisLift (i : Fin 6) (j : Fin 3) :
    smallParityTwoCandidate (smallParityThreeIndex i) :=
  smallParityThreeGeneratorLift i (smallParityThreeBasisPosition i j)

/-- The standard binary basis with the profile's coordinate ordering. -/
@[expose] public def smallParityThreeBinaryBasis (j : Fin 3) : SmallParityThreeQuotient :=
  Multiplicative.ofAdd (fun k => if k = j then 1 else 0)

/-- Correct images of the three specified lifts suffice for surjectivity. -/
public theorem smallParityThree_surjective_of_basis (i : Fin 6)
    (π : smallParityTwoCandidate (smallParityThreeIndex i) →* SmallParityThreeQuotient)
    (h : ∀ j, π (smallParityThreeBasisLift i j) = smallParityThreeBinaryBasis j) :
    Function.Surjective π := by
  intro v
  refine ⟨smallParityThreeBasisLift i 0 ^ (v.toAdd 0).val *
    smallParityThreeBasisLift i 1 ^ (v.toAdd 1).val *
    smallParityThreeBasisLift i 2 ^ (v.toAdd 2).val, ?_⟩
  simp only [map_mul, map_pow, h]
  exact (by decide +kernel : ∀ v : SmallParityThreeQuotient,
    smallParityThreeBinaryBasis 0 ^ (v.toAdd 0).val *
      smallParityThreeBinaryBasis 1 ^ (v.toAdd 1).val *
      smallParityThreeBinaryBasis 2 ^ (v.toAdd 2).val = v) v

end ReeTwo.SylowModel
