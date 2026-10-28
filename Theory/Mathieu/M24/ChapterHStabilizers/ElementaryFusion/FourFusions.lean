module

public import Theory.Mathieu.M24.ChapterHStabilizers.ElementaryFusion.Candidates

/-!
# Native fusion of four additional rank-five candidates

Four native Golay-code automorphisms send the five generators of each
additional Sylow candidate to explicit words in the sextet or trio candidate.
Closure induction proves subgroup containment. These are genuine ambient
conjugations; no normality of an arbitrary elementary subgroup is assumed.

Source: Aschbacher–Smith H.14.1(5), printed p.397. The finite witnesses were
found by GAP and are checked entirely by Lean's kernel.
-/

public section
namespace Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion
open M24LocalGeometry Subgroup

/-- The first two rows fuse into the sextet candidate and the other two into the trio. -/
@[expose] def fusionTarget (i : Fin 4) : Fin 2 := if i < 2 then 1 else 0

private def fusionPerm (i : Fin 4) : Equiv.Perm (Fin 24) where
  toFun := (![![2,3,0,1,16,23,15,14,18,12,17,22,9,21,7,6,4,10,8,20,19,13,11,5],![8,3,5,13,11,22,14,1,12,18,15,0,19,10,20,6,17,23,21,16,4,9,7,2],![12,10,6,18,20,15,4,7,13,22,14,1,8,11,0,9,19,17,21,16,23,2,5,3],![17,9,3,14,6,18,0,13,5,15,22,23,1,16,4,8,12,20,2,7,11,10,21,19]]) i
  invFun := (![![2,3,0,1,16,23,15,14,18,12,17,22,9,21,7,6,4,10,8,20,19,13,11,5],![11,7,23,1,20,2,15,22,0,21,13,4,8,3,6,10,19,16,9,12,14,18,5,17],![14,11,21,23,6,22,2,7,12,15,1,13,0,8,10,5,19,17,3,16,4,18,9,20],![6,12,18,2,14,8,4,19,15,1,21,20,16,7,3,9,13,0,5,23,17,22,10,11]]) i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

private def rowMessage : Fin 4 → Fin 12 → Fin 4096 := ![![2788,3176,1953,1298,720,2480,3872,1648,480,2960,3920,3280],![852,716,164,2192,1088,516,660,214,84,528,705,720],![781,556,361,32,769,13,316,936,2569,261,806,1573],![1298,896,30,1156,466,148,1159,3330,1460,1046,262,1424]]

private theorem fusion_rows : ∀ i j,
    m24PermuteMask (fusionPerm i) (m24GolayRow j) = m24GolayCode (rowMessage i j) := by
  decide +kernel

/-- Each fusion conjugator is an element of the literal native M24. -/
noncomputable def fusionElement (i : Fin 4) : M24 :=
  ⟨fusionPerm i, PairOvergroups.QuotientConstruction.AffineLiftConstruction.mem_M24_of_rows _
    (fun j => ⟨rowMessage i j, fusion_rows i j⟩)⟩

private def targetWord : Fin 4 → Fin 5 → List (Fin 6) := ![![[5,3,1],[5,3],[1,0],[3,2,1],[5,3,2,1,0]],![[2,0],[5,3,1,0],[4,3,1,0],[4,1],[5,4,1,0]],![[5,3,2,0],[5,3,2],[5,3],[3],[4,3,2,1,0]],![[4,2,1,0],[3],[1,0],[5,1,0],[5,4,3,1]]]

private noncomputable def evaluate (k : Fin 2) : List (Fin 6) → M24
  | [] => 1
  | a :: w => EvenCandidates.generator k a * evaluate k w

private theorem evaluate_mem (k : Fin 2) (w : List (Fin 6)) :
    evaluate k w ∈ EvenCandidates.elementary k := by
  induction w with
  | nil => exact (EvenCandidates.elementary k).one_mem
  | cons a w ih =>
      exact (EvenCandidates.elementary k).mul_mem (EvenCandidates.generator_mem k a) ih

private theorem evaluate_apply (k : Fin 2) (w : List (Fin 6)) (x : Fin 24) :
    (evaluate k w).val x = EvenCandidates.evaluatePoint k w x := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      change (EvenCandidates.generator k a).val ((evaluate k w).val x) = _
      rw [EvenCandidates.generator_apply, ih]
      rfl

private theorem generator_word_check : ∀ (i : Fin 4) (a : Fin 5) (x : Fin 24),
    fusionPerm i (SylowNormalizer.OrderEnumeration.point (smallGeneratorIndex i a)
      ((fusionPerm i).symm x)) =
        EvenCandidates.evaluatePoint (fusionTarget i) (targetWord i a) x := by
  decide +kernel

private theorem generator_word (i : Fin 4) (a : Fin 5) :
    (MulAut.conj (fusionElement i)) (smallGenerator i a) =
      evaluate (fusionTarget i) (targetWord i a) := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change fusionPerm i
    ((SylowNormalizer.OrderEnumeration.element (smallGeneratorIndex i a)).val.val
      ((fusionPerm i).symm x)) = _
  rw [SylowNormalizer.OrderEnumeration.element_apply, evaluate_apply]
  exact generator_word_check i a x

/-- Each of the four displayed five-generator groups is fused into an E64 candidate. -/
theorem smallCandidate_fusion (i : Fin 4) :
    (smallCandidate i).map (MulAut.conj (fusionElement i)).toMonoidHom ≤
      EvenCandidates.elementary (fusionTarget i) := by
  rw [Subgroup.map_le_iff_le_comap, smallCandidate, Subgroup.closure_le]
  rintro _ ⟨a, rfl⟩
  change (MulAut.conj (fusionElement i)) (smallGenerator i a) ∈
    EvenCandidates.elementary (fusionTarget i)
  rw [generator_word]
  exact evaluate_mem _ _

end Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion
