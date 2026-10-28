module

public import Theory.Mathieu.M12.SylowOvergroups.Tables

/-!
# Generation outside the two marked M₁₂ parabolics

For each of the 41 Sylow double-coset representatives outside the two marked
parabolics, short words in that representative and the three marked Sylow
generators recover both standard M₁₂ generators. The longest word has fourteen
letters. The words are untrusted data, checked against the actual permutations
by the Lean kernel. The existing permutation tables prevent repeated expansion
of the longer words defining the representatives.

`RankTwoGeneration/source/generate.py` reconstructs the words by breadth-first
search. No search result or external computation is used as a proof.
Source: GLS3 Table 5.3b; Aschbacher--Smith, 15.3.41--42, printed p.1138.
The permutation model and attribution are inherited from
`SmallParabolicPair.Seeds` and `SylowOvergroups.Representatives`.
-/

namespace Sporadic.Mathieu.M12SmallPair.SylowOvergroups

private def generationWords : Array (Fin 2 → List (Fin 4)) := #[
  ![[],[]],
  ![[3],[2,2,3,0,2,3,0,2,3,0,3,0,0]],
  ![[3,3,2,3,1,2,0],[3]],
  ![[3,0,3,1,2,1,3,3,3,2],[0,0,0,3,1,3,3,3,2,2]],
  ![[3,2,3,3,1,2,0],[3,3]],
  ![[0,2,2,3,3,0,2,3,0,1],[0,0,2,3,3,1,3,2,3]],
  ![[0,2,1,3,2,1,3,0],[3,0,1,3,2,3,1,3,3,2,3]],
  ![[1,2,3,0,0,0,2,3,0],[2,1,3,1,3,3,0,3]],
  ![[2,2,1,3,1,2,0,3,0],[1,3,1,2,3,1,2,3,2]],
  ![[3,0,2,3,0,2,2,3,2,3],[0,3,2,3,2,2,3,1,3,2,2,1]],
  ![[0,0,1,3,1,2,3,1,2,3,1],[1,3,0,2,0,3,0,2,3]],
  ![[1,3,2,3,2,3,0,2],[0,0,2,1,3,0,1,3,3]],
  ![[2,1,3,3,3,2,1,3,3,3],[3,3,3,0,1,3,2,1,3,3]],
  ![[1,3,0,0,1,2,3,3,1],[1,2,1,3,0,3,2,3,2]],
  ![[3,0,0,2,0,1,3,0,2,1,3],[1,2,1,3,2,2,1,3,0,3,2,3]],
  ![[0,2,2,3,1,3,0,3,0,1,3,2],[0,3,0,3,2,1,3,0,3,1,3,1,3,1]],
  ![[2,0,3,2,3,0,0,2,3],[3,3,3,3,0,3,2,3,0,0]],
  ![[0,0,3,0,2,2,2,3,1,3],[2,3,3,1,3,3,0,3,2]],
  ![[1,3,2,0,3,1,3,1,3,2,3],[0,3,3,3,3,2,2,3]],
  ![[0,2,2,1,3,0,3,1,3,0],[0,1,2,3,3,3,3,0,3,1,3]],
  ![[1,3,3,1,3,2,0,2],[3,0,2,3,3,0,2,0,3]],
  ![[0,3,3,0,0,3,2,1],[0,0,3,3,3,3,2,0,1,2]],
  ![[0,2,0,2,3,1,2,2,3,3],[2,2,2,3,3,0,0,2]],
  ![[0,1,3,2,0,3,0,3,2,0,3],[0,0,3,0,0,3,3,2,1]],
  ![[1,2,3,3,0,3,0,2,3,3,0],[0,2,3,2,2,1,3,1,2,2,3]],
  ![[0,3,0,3,0,1,3,0,3,1],[2,3,0,3,3,2,3,3,2,0,1]],
  ![[3,0,3,0,3,1,3,1,2,0],[3,1,3,0,3,1,2,0,3]],
  ![[0,1,3,1,3,1,3,0,3,1],[0,3,2,0,1,2,3,0,0,1,3,2]],
  ![[0,3,0,3,0,2,3,0,2,3],[1,3,3,0,0,3,3,1]],
  ![[3,0,1,3,3,1,2,1,3,0],[3,2,2,1,3,0,1,3]],
  ![[0,0,2,3,0,2,1,3,0,2],[0,2,0,3,0,2,1,3,3,0]],
  ![[0,0,1,2,3,1,3,2,0,1],[0,0,3,2,2,3,1,3,1]],
  ![[0,2,1,3,0,2,1,3,0,2,1],[3,1,3,2,3,0,2,3,2,2]],
  ![[0,0,0,3,3,3,2,1],[3,2,3,1,2,0,1,3,0,2]],
  ![[2,1,3,3,3,2,1,3,0],[3,0,0,3,1,3,3,0,2]],
  ![[0,0,3,3,2,2,3,2,0,3,0],[0,3,3,0,3,1,3,3,2,0]],
  ![[3,0,2,2,2,3,1,3,2],[3,2,0,3,0,3,3,2,0,3]],
  ![[],[]],
  ![[0,2,0,2,2,3,0,3,2,0],[0,0,1,3,0,3,0,1,3,3,2,0]],
  ![[0,1,2,2,3,0,3,1],[1,2,3,3,0,3,0,3,0]],
  ![[1,2,3,3,2,2,3,3,0,0],[3,0,3,3,0,3,3,1,3,0]],
  ![[],[]],
  ![[3,3,3,0,1,3,3,3,3,3],[1,3,1,3,2,3,2,2,3,3,3,3]],
  ![[2,2,2,3,3,3,3,3,0,3,3,0],[2,3,3,0,3,3,3,0,3,3,1]]]

private def generatorPerm (i : Fin 44) (j : Fin 4) : Equiv.Perm (Fin 12) :=
  ![sylowPerm 1, sylowPerm 2, sylowPerm 3, representativePerm i] j

private theorem localGenerator_perm (i : Fin 44) (j : Fin 4) :
    (localGenerator i j).val = generatorPerm i j := by
  fin_cases j
  · change leftIPerm = sylowPerm 1
    decide +kernel
  · change rightIPerm = sylowPerm 2
    decide +kernel
  · change movingActorPerm * leftIPerm * movingActorPerm = sylowPerm 3
    decide +kernel
  · exact representative_perm i

private def wordPerm (i : Fin 44) : List (Fin 4) → Equiv.Perm (Fin 12)
  | [] => 1
  | j :: w => generatorPerm i j * wordPerm i w

private theorem localWord_perm (i : Fin 44) (w : List (Fin 4)) :
    (localWord i w).val = wordPerm i w := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    change (localGenerator i j).val * (localWord i w).val = _
    rw [localGenerator_perm, ih]
    rfl

private theorem generation_check : ∀ i : Fin 44, i ≠ 0 → i ≠ 37 → i ≠ 41 →
    ∀ j : Fin 2, wordPerm i (generationWords[i.val]! j) =
      ![m12GeneratorA, m12GeneratorB] j := by
  decide +kernel

/-- Every representative outside the two parabolics recovers the two standard
model generators from itself and the marked Sylow subgroup. -/
public theorem standardGenerators_mem_of_representative
    (H : Subgroup M12) (hS : sylowCandidate ≤ H)
    (i : Fin 44) (hi : representative i ∈ H)
    (h0 : i ≠ 0) (h37 : i ≠ 37) (h41 : i ≠ 41) :
    ∀ j : Fin 2, standardGenerator j ∈ H := by
  intro j
  have he : localWord i (generationWords[i.val]! j) = standardGenerator j := by
    apply Subtype.ext
    rw [localWord_perm]
    fin_cases j <;> exact generation_check i h0 h37 h41 _
  exact he ▸ localWord_mem H hS i hi _

end Sporadic.Mathieu.M12SmallPair.SylowOvergroups
