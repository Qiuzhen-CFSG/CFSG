module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InvariantPoint.Native
public import Theory.Mathieu.M22.Properties.HexadSplitCoordinates

/-!
# Transversality of three native James point spaces

Twelve endpoint-star constraints at the points 1, 2, 3 form an invertible
binary matrix. Thus these three annihilator spaces have zero intersection.
The actual M22 three-transitive action and its triple-cover lift transport
this identity to every three distinct points, retaining the column action.

This supplies the native vanishing argument for the invariant complement
in Aschbacher--Segev (4.8), Invent. Math. 105 (1991), p.599,
DOI 10.1007/BF01232280. The original-core application is in Intersection.
The small matrices are derived from the existing ATLAS-based endpoint data
used by InvariantPoint.Native; its source attribution remains unchanged.
-/

@[expose] public section
noncomputable section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InvariantPoint
open Subgroup Sporadic.Mathieu M22TripleCover
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open CoreProjectiveAction
open Janko4.InvolutionCentralizers.First.QuotientExtension
open scoped Matrix

private def tripleRows : Matrix12 := fun i => packedVector
  (![20,611,52,853,74,3458,166,680,199,2267,207,3229] i)
private def tripleInverse : Matrix12 := fun i => packedVector
  (![3375,2426,1154,1280,1155,5,3178,3517,2420,2104,2962,1537] i)
private theorem triple_inverse : tripleInverse * tripleRows = 1 := by decide +kernel
private theorem triple_constraints (j : Fin 12) :
    let i : Fin 231 := ![3,3,11,11,14,14,28,28,35,35,37,37] j
    let p : Fin 22 := ![1,1,2,2,3,3,3,3,2,2,1,1] j
    (p=1 ∨ p=2 ∨ p=3) ∧ p ∈ endpointPair i ∧
      tripleRows j ∈ scalarLine (projectiveVector i) := by
  have hh : ∀ j : Fin 12,
      let i : Fin 231 := ![3,3,11,11,14,14,28,28,35,35,37,37] j
      let p : Fin 22 := ![1,1,2,2,3,3,3,3,2,2,1,1] j
      (p=1 ∨ p=2 ∨ p=3) ∧ p ∈ endpointPair i := by decide +kernel
  refine ⟨(hh j).1,(hh j).2,?_⟩
  fin_cases j
  · exact Or.inl rfl
  · apply Or.inr ∘ Or.inl
    decide +kernel
  · exact Or.inl rfl
  · apply Or.inr ∘ Or.inl
    decide +kernel
  · exact Or.inl rfl
  · apply Or.inr ∘ Or.inl
    decide +kernel
  · exact Or.inl rfl
  · apply Or.inr ∘ Or.inl
    decide +kernel
  · exact Or.inl rfl
  · apply Or.inr ∘ Or.inl
    decide +kernel
  · exact Or.inl rfl
  · apply Or.inr ∘ Or.inl
    decide +kernel

private theorem standard_triple_eq_zero (v : BinarySpace)
    (h1 : v ∈ pointSpace 1) (h2 : v ∈ pointSpace 2) (h3 : v ∈ pointSpace 3) : v=0 := by
  have hz : tripleRows *ᵥ v=0 := by
    funext j
    obtain ⟨hp,hi,hw⟩ := triple_constraints j
    rcases hp with hp | hp | hp
    · exact h1 _ (hp ▸ hi) _ hw
    · exact h2 _ (hp ▸ hi) _ hw
    · exact h3 _ (hp ▸ hi) _ hw
  have hh := congrArg (tripleInverse *ᵥ ·) hz
  rwa [Matrix.mulVec_mulVec,triple_inverse,Matrix.one_mulVec,Matrix.mulVec_zero] at hh

/-- Three distinct native point spaces have zero intersection. -/
theorem pointSpace_triple_eq_zero (p q r : Fin 22) (hpq : p≠q) (hpr : p≠r) (hqr : q≠r)
    (v : BinarySpace) (hp : v ∈ pointSpace p) (hq : v ∈ pointSpace q) (hr : v ∈ pointSpace r) : v=0 := by
  let source : Fin 3 ↪ Fin 22 := ⟨![p,q,r], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  let target : Fin 3 ↪ Fin 22 := ⟨![1,2,3],by decide +kernel⟩
  obtain ⟨g,hg⟩ := MulAction.isMultiplyPretransitive_iff.mp m22_isThreePretransitive source target
  obtain ⟨a,ha⟩ := M22TripleCover.Uniqueness.quotientMap_surjective g
  let b := coverInclusion a
  have hb (i : Fin 3) : pointAction b (source i) = target i := by
    rw [pointAction_cover]
    change (M22TripleCover.Uniqueness.quotientMap a).val (source i) = target i
    rw [ha]
    exact congrArg (fun e : Fin 3 ↪ Fin 22 => e i) hg
  have hbp : pointAction b p=1 := hb 0
  have hbq : pointAction b q=2 := hb 1
  have hbr : pointAction b r=3 := hb 2
  have hp' := pointSpace_transport b p v hp
  have hq' := pointSpace_transport b q v hq
  have hr' := pointSpace_transport b r v hr
  rw [hbp] at hp'
  rw [hbq] at hq'
  rw [hbr] at hr'
  have hz := standard_triple_eq_zero _ hp' hq' hr'
  have hh := congrArg (M22TripleCover.Ambient.binaryAction b⁻¹) hz
  rwa [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,
    Module.End.one_apply,map_zero] at hh

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InvariantPoint
end
