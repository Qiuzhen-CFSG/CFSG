module
public import Theory.Representation.BinarySevenCode.PermutationAction
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
/-!
# Weight orbits of the seven-letter even-word action

The alternating group is transitive on subsets of fixed size. Over the
binary field the support determines a word, so equality of weights is
exactly conjugacy in the natural A₇ action. This gives the three nonzero
orbits required in the local analysis, without enumerating A₇.

Source: Aschbacher--Smith, 12.3.4--5, printed pp.808--809.
-/

public section
open scoped Pointwise
namespace BinarySevenCode

theorem exists_alternating_of_weight_eq (v w : EvenWord)
    (hweight : weight v.val = weight w.val) :
    ∃ a : alternatingGroup (Fin 7), evenRepresentation a.val v = w := by
  let s : Set.powersetCard (Fin 7) (weight v.val) :=
    ⟨Finset.univ.filter (fun i => v.val i ≠ 0), rfl⟩
  let t : Set.powersetCard (Fin 7) (weight v.val) :=
    ⟨Finset.univ.filter (fun i => w.val i ≠ 0), hweight.symm⟩
  let : MulAction.IsPretransitive (alternatingGroup (Fin 7))
      (Set.powersetCard (Fin 7) (weight v.val)) :=
    Set.powersetCard.isPretransitive_alternatingGroup (by simp)
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) s t
  refine ⟨a, ?_⟩
  apply Subtype.ext
  funext i
  have hmem : i ∈ (a • s : Set.powersetCard (Fin 7) (weight v.val)).val ↔
      i ∈ t.val := by rw [ha]
  change i ∈ a • s.val ↔ i ∈ t.val at hmem
  rw [Finset.mem_smul_finset] at hmem
  have hs : (∃ y ∈ s.val, a • y = i) ↔ v.val (a.val.symm i) ≠ 0 := by
    constructor
    · rintro ⟨j,hj,hji⟩
      change a.val j = i at hji
      have he : j = a.val.symm i := a.val.injective (by simpa using hji)
      simpa only [s,Finset.mem_filter,Finset.mem_univ,true_and,he] using hj
    · intro hv
      refine ⟨a.val.symm i, ?_, ?_⟩
      · simpa only [s,Finset.mem_filter,Finset.mem_univ,true_and] using hv
      · exact a.val.apply_symm_apply i
  rw [hs] at hmem
  have he : v.val (a.val.symm i) ≠ 0 ↔ w.val i ≠ 0 := by
    simpa only [t,Finset.mem_filter,Finset.mem_univ,true_and] using hmem
  exact (by decide : ∀ a b : ZMod 2, (a ≠ 0 ↔ b ≠ 0) → a = b) _ _ he

theorem exists_alternating_iff_weight_eq (v w : EvenWord) :
    (∃ a : alternatingGroup (Fin 7), evenRepresentation a.val v = w) ↔
      weight v.val = weight w.val := by
  constructor
  · rintro ⟨a,rfl⟩
    exact (weight_evenRepresentation a.val v).symm
  · exact exists_alternating_of_weight_eq v w

end BinarySevenCode
