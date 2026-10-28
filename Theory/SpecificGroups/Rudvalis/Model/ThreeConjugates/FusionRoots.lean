module

public import Theory.SpecificGroups.Rudvalis.Model.ThreeConjugates.FusionData
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.LocalOrder.Maps
public import Theory.SpecificGroups.Rudvalis.Model.FivePointBase

/-!
# Fusing the fifteen marked Sylow involutions

Each word uses its actual binary normal-form representative together with
`a`, `b` and `b⁻¹`. It conjugates that representative to `a` or `b²`.
The words were found using odd-order products of involutions; only their
literal equations on the certified five-point base enter the proof.
Source and permutation convention: `Model.PermutationData` and `Sylow.Candidate`.
-/

namespace Rudvalis.ThreeConjugates.FusionCertificate

-- Keep the measured finite reductions sequential.
set_option Elab.async false
open SylowOvergroups.RadicalCoverage.SylowCertificate
open SylowOvergroups.RadicalCoverage.SylowCertificate.LocalOrder

@[expose] public def rootIndex : Fin 15 → Fin 16384 :=
  ![1, 2, 4, 12, 36, 64, 126, 152, 192, 256, 294, 1536, 2048, 6144, 10240]

@[expose] public def rootClass : Fin 15 → Bool :=
  ![true, true, true, true, true, true, false, false, true, true, false, true, true, true, true]

@[expose] public def marked (j : Fin 15) : Model :=
  if rootClass j then b^2 else a

@[expose] public def markedMap (j : Fin 15) (x : Fin 4060) : Fin 4060 :=
  if rootClass j then Data.bMap (Data.bMap x) else Data.aMap x

private theorem marked_smul (j : Fin 15) (x : Fin 4060) :
    marked j • x = markedMap j x := by
  unfold marked markedMap
  split <;> rfl

@[expose] public def rootLetter (j : Fin 15) : Fin 4 → Model :=
  ![candidateNormalForm (rootIndex j), a, b, b⁻¹]

@[expose] public def rootLetterMap (j : Fin 15) : Fin 4 → Fin 4060 → Fin 4060 :=
  ![normalMap (rootIndex j), Data.aMap, Data.bMap,
    fun x => Data.bMap (Data.bMap (Data.bMap x))]

private theorem rootLetter_smul (j : Fin 15) (i : Fin 4) (x : Fin 4060) :
    rootLetter j i • x = rootLetterMap j i x := by
  fin_cases i
  · exact normal_smul _ x
  · rfl
  · rfl
  · rfl

@[expose] public def rootWord : Fin 15 → List (Fin 4) :=
  ![[1, 2, 1, 2, 1, 1, 2, 2, 0, 3, 3, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 2, 0, 3, 3, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 2, 0, 3, 3, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 2, 0, 3, 3, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 2, 0, 3, 3, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 2, 0, 3, 3, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 2],
    [2, 2, 2, 2, 1, 2, 1, 1, 0, 1, 1, 3, 1, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 1, 2, 1, 1, 0, 1, 1, 3, 1, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 1, 2, 1, 1, 0, 1, 1, 3, 1, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 1, 2, 1, 1, 0, 1, 1, 3, 1, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 1, 2, 1, 1, 0, 1, 1, 3, 1, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 1, 2, 1, 1, 0, 1, 1, 3, 1, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 1, 2, 1, 1],
    [1, 2, 1, 1, 1, 1, 1, 2, 0, 3, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 2, 0, 3, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 2, 0, 3, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 2],
    [2, 1, 2, 2, 2, 2, 1, 1, 0, 1, 1, 3, 3, 3, 3, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2, 1, 1, 0, 1, 1, 3, 3, 3, 3, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2, 1, 1, 0, 1, 1, 3, 3, 3, 3, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2, 1, 1, 0, 1, 1, 3, 3, 3, 3, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2, 1, 1, 0, 1, 1, 3, 3, 3, 3, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2, 1, 1, 0, 1, 1, 3, 3, 3, 3, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2, 1, 1],
    [2, 2, 2, 1, 2, 1, 2, 2, 0, 3, 3, 1, 3, 1, 3, 3, 3, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 0, 3, 3, 1, 3, 1, 3, 3, 3, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 0, 3, 3, 1, 3, 1, 3, 3, 3, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2],
    [1, 2, 2, 1, 2, 1, 1, 2, 0, 3, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 2, 0, 3, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 2],
    [1, 2, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1],
    [1, 1, 2, 2, 1, 1, 1, 2, 0, 3, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 0, 3, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 0, 3, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 0, 3, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 0, 3, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 0, 3, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 0, 3, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 0, 3, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 0, 3, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 0, 3, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 0, 3, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 0, 3, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 0, 3, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 0, 3, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2],
    [2, 1, 2, 2, 1, 1, 1, 2, 0, 3, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 2, 2, 1, 1, 1, 2, 0, 3, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 2, 2, 1, 1, 1, 2, 0, 3, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 2, 2, 1, 1, 1, 2],
    [2, 1, 2, 2, 2, 1, 1, 2, 0, 3, 1, 1, 3, 3, 3, 1, 3, 2, 2, 2, 1, 2, 2, 2, 1, 1, 2, 0, 3, 1, 1, 3, 3, 3, 1, 3, 2, 2, 2, 1, 2, 2, 2, 1, 1, 2],
    [1, 1, 2, 1, 2, 1, 2, 1, 0, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 0, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 0, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1],
    [2, 1, 2, 2, 2, 1, 2, 1, 0, 1, 3, 1, 3, 3, 3, 1, 3, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1],
    [1, 1, 2, 1, 1, 2, 1, 1, 0, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 0, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 0, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 0, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 0, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 0, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1],
    [2, 1, 2, 2, 2, 2, 2, 1, 0, 1, 3, 3, 3, 3, 3, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2, 2, 1, 0, 1, 3, 3, 3, 3, 3, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2, 2, 1, 0, 1, 3, 3, 3, 3, 3, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2, 2, 1, 0, 1, 3, 3, 3, 3, 3, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2, 2, 1, 0, 1, 3, 3, 3, 3, 3, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2, 2, 1, 0, 1, 3, 3, 3, 3, 3, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2, 2, 1],
    [2, 2, 2, 1, 2, 1, 2, 1, 0, 1, 3, 1, 3, 1, 3, 3, 3, 2, 2, 2, 2, 2, 1, 2, 1, 2, 1, 0, 1, 3, 1, 3, 1, 3, 3, 3, 2, 2, 2, 2, 2, 1, 2, 1, 2, 1, 0, 1, 3, 1, 3, 1, 3, 3, 3, 2, 2, 2, 2, 2, 1, 2, 1, 2, 1, 0, 1, 3, 1, 3, 1, 3, 3, 3, 2, 2, 2, 2, 2, 1, 2, 1, 2, 1, 0, 1, 3, 1, 3, 1, 3, 3, 3, 2, 2, 2, 2, 2, 1, 2, 1, 2, 1, 0, 1, 3, 1, 3, 1, 3, 3, 3, 2, 2, 2, 2, 2, 1, 2, 1, 2, 1]]

@[expose] public def rootConjugator (j : Fin 15) : Model :=
  ((rootWord j).map (rootLetter j)).prod

private theorem rootConjugator_smul (j : Fin 15) (x : Fin 4060) :
    rootConjugator j • x = evalWord (rootLetterMap j) (rootWord j) x :=
  prod_smul _ _ (rootLetter_smul j) _ x

@[expose] public def RootTest (j : Fin 15) : Prop :=
  ∀ i : Fin 5,
    evalWord (rootLetterMap j) (rootWord j) (normalMap (rootIndex j) (i.castLE (by decide))) =
      markedMap j (evalWord (rootLetterMap j) (rootWord j) (i.castLE (by decide)))

public instance (j : Fin 15) : Decidable (RootTest j) :=
  inferInstanceAs (Decidable (∀ _ : Fin 5, _))

set_option maxRecDepth 3000 in
private theorem root_test_0 : RootTest 0 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem root_test_1 : RootTest 1 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem root_test_2 : RootTest 2 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem root_test_3 : RootTest 3 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem root_test_4 : RootTest 4 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem root_test_5 : RootTest 5 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem root_test_6 : RootTest 6 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem root_test_7 : RootTest 7 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem root_test_8 : RootTest 8 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem root_test_9 : RootTest 9 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem root_test_10 : RootTest 10 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem root_test_11 : RootTest 11 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem root_test_12 : RootTest 12 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem root_test_13 : RootTest 13 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem root_test_14 : RootTest 14 := by decide +kernel

private theorem root_test (j : Fin 15) : RootTest j := by
  fin_cases j
  · exact root_test_0
  · exact root_test_1
  · exact root_test_2
  · exact root_test_3
  · exact root_test_4
  · exact root_test_5
  · exact root_test_6
  · exact root_test_7
  · exact root_test_8
  · exact root_test_9
  · exact root_test_10
  · exact root_test_11
  · exact root_test_12
  · exact root_test_13
  · exact root_test_14

/-- Every marked root is conjugate to its explicitly specified ambient involution. -/
public theorem root_isConj (j : Fin 15) :
    IsConj (candidateNormalForm (rootIndex j)) (marked j) := by
  apply isConj_iff.mpr
  refine ⟨rootConjugator j, mul_inv_eq_iff_eq_mul.mpr ?_⟩
  apply eq_of_smul_first_five
  intro i
  simpa only [mul_smul, rootConjugator_smul, normal_smul, marked_smul] using root_test j i

/-- The marked roots in the forest are covered by the two actual representatives. -/
public theorem root_fusion (n : Fin 16384) (hn : n ∈ roots) :
    IsConj (candidateNormalForm n) a ∨ IsConj (candidateNormalForm n) (b^2) := by
  have hr : ∃ j : Fin 15, rootIndex j = n := by
    simp only [roots, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩
    · exact ⟨8, rfl⟩
    · exact ⟨9, rfl⟩
    · exact ⟨10, rfl⟩
    · exact ⟨11, rfl⟩
    · exact ⟨12, rfl⟩
    · exact ⟨13, rfl⟩
    · exact ⟨14, rfl⟩
  obtain ⟨j, rfl⟩ := hr
  have h := root_isConj j
  unfold marked at h
  split at h
  · exact Or.inr h
  · exact Or.inl h

end Rudvalis.ThreeConjugates.FusionCertificate
