module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Involutions.Data
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Basic
public import Theory.SpecificGroups.Rudvalis.Model.FivePointBase

/-!
# Roots of the max4 involution forest

Twelve representatives centralize the three generators of the marked eight,
so they belong to the intrinsic core. Explicit ambient words conjugate the
other three representatives to its nonidentity first generator. Every
equality is checked on the certified five-point base of the actual model.

Source: Aschbacher--Smith J.2.6(2), printed pp.434--435. The concrete
certificate uses the unchanged ATLAS words and inverse point-action convention
in `LocalCover.ElementaryCatalogue`. See `Involutions/source/README.md`.
-/

namespace Rudvalis.CoveringIncidence.Max4InvolutionCertificate
open SylowOvergroups.RadicalCoverage.LocalCover
open CatalogueCertificate

set_option Elab.async false
open Subgroup

@[expose] public def coreIndex : Fin 12 → Fin 16384 :=
  ![13, 37, 64, 158, 211, 390, 600, 768, 1536, 3008, 4096, 12288]

@[expose] public def CoreTest (j : Fin 12) : Prop :=
  ∀ k : Fin 3, ∀ i : Fin 5,
    elementaryPermutation (k.castLE (by decide))
        (normalMap (coreIndex j) (i.castLE (by decide))) =
      normalMap (coreIndex j)
        (elementaryPermutation (k.castLE (by decide)) (i.castLE (by decide)))

public instance (j : Fin 12) : Decidable (CoreTest j) :=
  inferInstanceAs (Decidable (∀ _ : Fin 3, ∀ _ : Fin 5, _))

set_option maxRecDepth 3000 in
private theorem core_test_0 : CoreTest 0 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem core_test_1 : CoreTest 1 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem core_test_2 : CoreTest 2 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem core_test_3 : CoreTest 3 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem core_test_4 : CoreTest 4 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem core_test_5 : CoreTest 5 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem core_test_6 : CoreTest 6 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem core_test_7 : CoreTest 7 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem core_test_8 : CoreTest 8 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem core_test_9 : CoreTest 9 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem core_test_10 : CoreTest 10 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem core_test_11 : CoreTest 11 := by decide +kernel

private theorem core_test (j : Fin 12) : CoreTest j := by
  fin_cases j
  · exact core_test_0
  · exact core_test_1
  · exact core_test_2
  · exact core_test_3
  · exact core_test_4
  · exact core_test_5
  · exact core_test_6
  · exact core_test_7
  · exact core_test_8
  · exact core_test_9
  · exact core_test_10
  · exact core_test_11

public theorem root_mem_core (j : Fin 12) : normalForm (coreIndex j) ∈ max4Core := by
  rw [max4Core_eq_centralizer]
  refine ⟨localP_le_max4 (normalForm_mem _), ?_⟩
  have he (k : Fin 3) : elementaryGenerator (k.castLE (by decide)) * normalForm (coreIndex j) =
      normalForm (coreIndex j) * elementaryGenerator (k.castLE (by decide)) := by
    apply eq_of_smul_first_five
    intro i
    simpa only [mul_smul, elementary_smul, normal_smul] using core_test j k i
  change normalForm (coreIndex j) ∈ centralizer
    (closure {elementaryGenerator 0, elementaryGenerator 1, elementaryGenerator 2} : Set Model)
  rw [centralizer_closure, mem_centralizer_iff]
  intro c hc
  rcases hc with rfl | rfl | rfl
  · exact he 0
  · exact he 1
  · exact he 2

@[expose] public def fusionIndex : Fin 3 → Fin 16384 :=
  ![2, 8, 128]

@[expose] public def rootLetter (j : Fin 3) : Fin 5 → Model :=
  ![normalForm (fusionIndex j), a, b, b⁻¹, elementaryGenerator 0]

@[expose] public def rootLetterMap (j : Fin 3) : Fin 5 → Fin 4060 → Fin 4060 :=
  ![normalMap (fusionIndex j), Data.aMap, Data.bMap,
    fun x => Data.bMap (Data.bMap (Data.bMap x)), elementaryPermutation 0]

private theorem rootLetter_smul (j : Fin 3) (i : Fin 5) (x : Fin 4060) :
    rootLetter j i • x = rootLetterMap j i x := by
  fin_cases i
  · exact normal_smul _ x
  · rfl
  · rfl
  · rfl
  · exact elementary_smul _ x

@[expose] public def rootWord : Fin 3 → List (Fin 5) :=
  ![[2, 1, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 1, 1, 1, 1], [2, 1, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 1, 1, 1, 1], [1, 1, 1, 2, 2, 2, 1, 1, 0, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 1, 0, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 1, 0, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 1, 0, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 1, 0, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 1, 0, 1, 1, 3, 3, 3, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 1]]

@[expose] public def rootConjugator (j : Fin 3) : Model :=
  ((rootWord j).map (rootLetter j)).prod

@[expose] public def rootConjugatorMap (j : Fin 3) (x : Fin 4060) : Fin 4060 :=
  (rootWord j).foldr (fun i y => rootLetterMap j i y) x

private theorem rootConjugator_smul (j : Fin 3) (x : Fin 4060) :
    rootConjugator j • x = rootConjugatorMap j x := by
  have h (l : List (Fin 5)) (x : Fin 4060) :
      (l.map (rootLetter j)).prod • x = l.foldr (fun i y => rootLetterMap j i y) x := by
    induction l generalizing x with
    | nil => exact one_smul Model x
    | cons i l ih =>
      change (rootLetter j i * (l.map (rootLetter j)).prod) • x = _
      rw [mul_smul, ih, rootLetter_smul]
      rfl
  exact h _ x

@[expose] public def RootTest (j : Fin 3) : Prop :=
  ∀ i : Fin 5,
    rootConjugatorMap j (normalMap (fusionIndex j) (i.castLE (by decide))) =
      elementaryPermutation 0 (rootConjugatorMap j (i.castLE (by decide)))

public instance (j : Fin 3) : Decidable (RootTest j) :=
  inferInstanceAs (Decidable (∀ _ : Fin 5, _))

set_option maxRecDepth 3000 in
private theorem root_test_0 : RootTest 0 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem root_test_1 : RootTest 1 := by decide +kernel

set_option maxRecDepth 3000 in
private theorem root_test_2 : RootTest 2 := by decide +kernel

private theorem root_test (j : Fin 3) : RootTest j := by
  fin_cases j
  · exact root_test_0
  · exact root_test_1
  · exact root_test_2

public theorem root_isConj (j : Fin 3) :
    IsConj (normalForm (fusionIndex j)) (elementaryGenerator 0) := by
  apply isConj_iff.mpr
  refine ⟨rootConjugator j, mul_inv_eq_iff_eq_mul.mpr ?_⟩
  apply eq_of_smul_first_five
  intro i
  simpa only [mul_smul, rootConjugator_smul, normal_smul, elementary_smul] using root_test j i

public theorem root_alternative (n : Fin 16384) (hn : n ∈ roots) :
    normalForm n ∈ max4Core ∨ IsConj (normalForm n) (elementaryGenerator 0) := by
  simp only [roots, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (root_isConj 0)
  · exact Or.inr (root_isConj 1)
  · exact Or.inl (root_mem_core 0)
  · exact Or.inl (root_mem_core 1)
  · exact Or.inl (root_mem_core 2)
  · exact Or.inr (root_isConj 2)
  · exact Or.inl (root_mem_core 3)
  · exact Or.inl (root_mem_core 4)
  · exact Or.inl (root_mem_core 5)
  · exact Or.inl (root_mem_core 6)
  · exact Or.inl (root_mem_core 7)
  · exact Or.inl (root_mem_core 8)
  · exact Or.inl (root_mem_core 9)
  · exact Or.inl (root_mem_core 10)
  · exact Or.inl (root_mem_core 11)

public theorem marked_ne_one : elementaryGenerator 0 ≠ 1 := by
  intro h
  have he := congrArg (fun g : Model => g • (0 : Fin 4060)) h
  have hn : elementaryPermutation 0 (0 : Fin 4060) ≠ 0 := by decide +kernel
  exact hn (by simpa only [elementary_smul, one_smul] using he)

public theorem marked_mem : elementaryGenerator 0 ∈ elementary 2 := by
  apply Subgroup.subset_closure
  simp

end Rudvalis.CoveringIncidence.Max4InvolutionCertificate
