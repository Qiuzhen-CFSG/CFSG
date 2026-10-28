module
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointExtension.Coordinates
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointExtension.Generators
public import Mathlib.Tactic

/-!
# The centralizer of the three point-intersection words

In the heart coordinates, an endomorphism commuting with the three words
`aba`, `bab³`, and `b³ab` lies in the span of the identity and the swap of
coordinates 0 and 6. The only invertible possibilities are those two matrices.

The proof extracts 98 matrix-entry equations, performs explicit binary
elimination, and substitutes back to determine every entry. Each equation and
linear combination is checked in Lean; the support table is checked against
the actual permutation action on the augmentation quotient. No enumeration
of GL(10,2) or externally trusted computation is used.

This supplies the centralizer step in the extension proof for James's M₁₂
module, cited in Aschbacher--Smith G.7.3(2), printed p.348 (PDF p.359),
G. D. James, J. Algebra 27 (1973), 57--111.
-/

@[expose] public section
namespace Representation.MathieuSmall.M12Recognition.PointExtension

def wordSupport (k : Fin 3) (i : Fin 10) : List Nat :=
  match k.val, i.val with
  | 0, 0 => [1, 2, 3, 4, 5, 6, 7, 8, 9]
  | 0, 1 => [0, 1, 2, 3, 4, 5, 6, 7, 8]
  | 0, 2 => [0, 1, 2, 4, 5, 6, 7, 8, 9]
  | 0, 3 => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  | 0, 4 => [0, 1, 2, 3, 5, 6, 7, 8, 9]
  | 0, 5 => [0, 2, 3, 4, 5, 6, 7, 8, 9]
  | 0, 6 => [0, 1, 2, 3, 4, 5, 7, 8, 9]
  | 0, 7 => [0, 1, 2, 3, 4, 5, 6, 8, 9]
  | 0, 8 => [0, 1, 2, 3, 4, 6, 7, 8, 9]
  | 0, 9 => [0, 1, 2, 3, 4, 5, 6, 7, 9]
  | 1, 0 => [0, 4]
  | 1, 1 => [4, 7]
  | 1, 2 => [3, 4]
  | 1, 3 => [2, 4]
  | 1, 4 => [4]
  | 1, 5 => [4, 8]
  | 1, 6 => [4, 6]
  | 1, 7 => [1, 4]
  | 1, 8 => [4, 5]
  | 1, 9 => [4, 9]
  | 2, 0 => [0, 9]
  | 2, 1 => [5, 9]
  | 2, 2 => [8, 9]
  | 2, 3 => [7, 9]
  | 2, 4 => [4, 9]
  | 2, 5 => [1, 9]
  | 2, 6 => [6, 9]
  | 2, 7 => [3, 9]
  | 2, 8 => [2, 9]
  | 2, 9 => [9]
  | _, _ => []

def wordMatrix (k : Fin 3) : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  fun i j => if j.val ∈ wordSupport k i then 1 else 0

theorem wordMatrix_check (k : Fin 3) : permutationMatrix (wordPerm k) = wordMatrix k := by
  ext i j
  rw [permutationMatrix_formula]
  have h : ∀ (k : Fin 3) (i j : Fin 10),
      (((if Fin.castAdd 2 i = wordPerm k (Fin.castAdd 2 j) then 1 else 0) +
        (if Fin.castAdd 2 i = wordPerm k 11 then 1 else 0)) +
      ((if (10 : Fin 12) = wordPerm k (Fin.castAdd 2 j) then 1 else 0) +
        (if (10 : Fin 12) = wordPerm k 11 then 1 else 0)) : ZMod 2) = wordMatrix k i j := by
    exact @of_decide_eq_true _
      (@Nat.decidableForallFin 3 _ fun k => @Nat.decidableForallFin 10 _ fun i =>
        @Nat.decidableForallFin 10 _ fun j => ZMod.decidableEq 2 _ _) (by decide +kernel)
  exact h k i j

private theorem equation_100 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 0 = C 0 0 + C 4 0 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 0 0) (h 1).eq
  change (∑ l : Fin 10, C 0 l * wordMatrix 1 l 0) =
    (∑ l : Fin 10, wordMatrix 1 0 l * C l 0) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_106 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 6 = C 0 6 + C 4 6 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 0 6) (h 1).eq
  change (∑ l : Fin 10, C 0 l * wordMatrix 1 l 6) =
    (∑ l : Fin 10, wordMatrix 1 0 l * C l 6) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_109 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 9 = C 0 9 + C 4 9 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 0 9) (h 1).eq
  change (∑ l : Fin 10, C 0 l * wordMatrix 1 l 9) =
    (∑ l : Fin 10, wordMatrix 1 0 l * C l 9) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_200 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 0 = C 0 0 + C 9 0 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 0 0) (h 2).eq
  change (∑ l : Fin 10, C 0 l * wordMatrix 2 l 0) =
    (∑ l : Fin 10, wordMatrix 2 0 l * C l 0) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_204 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 4 = C 0 4 + C 9 4 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 0 4) (h 2).eq
  change (∑ l : Fin 10, C 0 l * wordMatrix 2 l 4) =
    (∑ l : Fin 10, wordMatrix 2 0 l * C l 4) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_206 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 6 = C 0 6 + C 9 6 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 0 6) (h 2).eq
  change (∑ l : Fin 10, C 0 l * wordMatrix 2 l 6) =
    (∑ l : Fin 10, wordMatrix 2 0 l * C l 6) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_141 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 7 = C 4 1 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 4 1) (h 1).eq
  change (∑ l : Fin 10, C 4 l * wordMatrix 1 l 1) =
    (∑ l : Fin 10, wordMatrix 1 4 l * C l 1) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_142 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 3 = C 4 2 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 4 2) (h 1).eq
  change (∑ l : Fin 10, C 4 l * wordMatrix 1 l 2) =
    (∑ l : Fin 10, wordMatrix 1 4 l * C l 2) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_145 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 8 = C 4 5 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 4 5) (h 1).eq
  change (∑ l : Fin 10, C 4 l * wordMatrix 1 l 5) =
    (∑ l : Fin 10, wordMatrix 1 4 l * C l 5) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_291 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 5 = C 9 1 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 9 1) (h 2).eq
  change (∑ l : Fin 10, C 9 l * wordMatrix 2 l 1) =
    (∑ l : Fin 10, wordMatrix 2 9 l * C l 1) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_292 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 8 = C 9 2 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 9 2) (h 2).eq
  change (∑ l : Fin 10, C 9 l * wordMatrix 2 l 2) =
    (∑ l : Fin 10, wordMatrix 2 9 l * C l 2) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_293 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 7 = C 9 3 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 9 3) (h 2).eq
  change (∑ l : Fin 10, C 9 l * wordMatrix 2 l 3) =
    (∑ l : Fin 10, wordMatrix 2 9 l * C l 3) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_110 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 0 = C 4 0 + C 7 0 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 1 0) (h 1).eq
  change (∑ l : Fin 10, C 1 l * wordMatrix 1 l 0) =
    (∑ l : Fin 10, wordMatrix 1 1 l * C l 0) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_116 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 6 = C 4 6 + C 7 6 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 1 6) (h 1).eq
  change (∑ l : Fin 10, C 1 l * wordMatrix 1 l 6) =
    (∑ l : Fin 10, wordMatrix 1 1 l * C l 6) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_119 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 9 = C 4 9 + C 7 9 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 1 9) (h 1).eq
  change (∑ l : Fin 10, C 1 l * wordMatrix 1 l 9) =
    (∑ l : Fin 10, wordMatrix 1 1 l * C l 9) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_120 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 0 = C 3 0 + C 4 0 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 2 0) (h 1).eq
  change (∑ l : Fin 10, C 2 l * wordMatrix 1 l 0) =
    (∑ l : Fin 10, wordMatrix 1 2 l * C l 0) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_126 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 6 = C 3 6 + C 4 6 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 2 6) (h 1).eq
  change (∑ l : Fin 10, C 2 l * wordMatrix 1 l 6) =
    (∑ l : Fin 10, wordMatrix 1 2 l * C l 6) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_129 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 9 = C 3 9 + C 4 9 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 2 9) (h 1).eq
  change (∑ l : Fin 10, C 2 l * wordMatrix 1 l 9) =
    (∑ l : Fin 10, wordMatrix 1 2 l * C l 9) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_150 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 0 = C 4 0 + C 8 0 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 5 0) (h 1).eq
  change (∑ l : Fin 10, C 5 l * wordMatrix 1 l 0) =
    (∑ l : Fin 10, wordMatrix 1 5 l * C l 0) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_156 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 6 = C 4 6 + C 8 6 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 5 6) (h 1).eq
  change (∑ l : Fin 10, C 5 l * wordMatrix 1 l 6) =
    (∑ l : Fin 10, wordMatrix 1 5 l * C l 6) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_159 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 9 = C 4 9 + C 8 9 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 5 9) (h 1).eq
  change (∑ l : Fin 10, C 5 l * wordMatrix 1 l 9) =
    (∑ l : Fin 10, wordMatrix 1 5 l * C l 9) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_214 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 4 = C 5 4 + C 9 4 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 1 4) (h 2).eq
  change (∑ l : Fin 10, C 1 l * wordMatrix 2 l 4) =
    (∑ l : Fin 10, wordMatrix 2 1 l * C l 4) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_224 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 4 = C 8 4 + C 9 4 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 2 4) (h 2).eq
  change (∑ l : Fin 10, C 2 l * wordMatrix 2 l 4) =
    (∑ l : Fin 10, wordMatrix 2 2 l * C l 4) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_230 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 0 = C 7 0 + C 9 0 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 3 0) (h 2).eq
  change (∑ l : Fin 10, C 3 l * wordMatrix 2 l 0) =
    (∑ l : Fin 10, wordMatrix 2 3 l * C l 0) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_234 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 4 = C 7 4 + C 9 4 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 3 4) (h 2).eq
  change (∑ l : Fin 10, C 3 l * wordMatrix 2 l 4) =
    (∑ l : Fin 10, wordMatrix 2 3 l * C l 4) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_236 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 6 = C 7 6 + C 9 6 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 3 6) (h 2).eq
  change (∑ l : Fin 10, C 3 l * wordMatrix 2 l 6) =
    (∑ l : Fin 10, wordMatrix 2 3 l * C l 6) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_220 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 0 = C 8 0 + C 9 0 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 2 0) (h 2).eq
  change (∑ l : Fin 10, C 2 l * wordMatrix 2 l 0) =
    (∑ l : Fin 10, wordMatrix 2 2 l * C l 0) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_226 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 6 = C 8 6 + C 9 6 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 2 6) (h 2).eq
  change (∑ l : Fin 10, C 2 l * wordMatrix 2 l 6) =
    (∑ l : Fin 10, wordMatrix 2 2 l * C l 6) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_194 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 0 + C 9 1 + C 9 2 + C 9 3 + C 9 4 + C 9 5 + C 9 6 + C 9 7 + C 9 8 + C 9 9 = C 4 4 + C 9 4 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 9 4) (h 1).eq
  change (∑ l : Fin 10, C 9 l * wordMatrix 1 l 4) =
    (∑ l : Fin 10, wordMatrix 1 9 l * C l 4) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_44 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 0 + C 4 1 + C 4 2 + C 4 3 + C 4 5 + C 4 6 + C 4 7 + C 4 8 + C 4 9 = C 0 4 + C 1 4 + C 2 4 + C 3 4 + C 5 4 + C 6 4 + C 7 4 + C 8 4 + C 9 4 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 4 4) (h 0).eq
  change (∑ l : Fin 10, C 4 l * wordMatrix 0 l 4) =
    (∑ l : Fin 10, wordMatrix 0 4 l * C l 4) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_94 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 0 + C 9 1 + C 9 2 + C 9 3 + C 9 5 + C 9 6 + C 9 7 + C 9 8 + C 9 9 = C 0 4 + C 1 4 + C 2 4 + C 3 4 + C 4 4 + C 5 4 + C 6 4 + C 7 4 + C 9 4 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 9 4) (h 0).eq
  change (∑ l : Fin 10, C 9 l * wordMatrix 0 l 4) =
    (∑ l : Fin 10, wordMatrix 0 9 l * C l 4) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_102 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 3 = C 0 2 + C 4 2 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 0 2) (h 1).eq
  change (∑ l : Fin 10, C 0 l * wordMatrix 1 l 2) =
    (∑ l : Fin 10, wordMatrix 1 0 l * C l 2) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_107 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 1 = C 0 7 + C 4 7 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 0 7) (h 1).eq
  change (∑ l : Fin 10, C 0 l * wordMatrix 1 l 7) =
    (∑ l : Fin 10, wordMatrix 1 0 l * C l 7) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_108 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 5 = C 0 8 + C 4 8 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 0 8) (h 1).eq
  change (∑ l : Fin 10, C 0 l * wordMatrix 1 l 8) =
    (∑ l : Fin 10, wordMatrix 1 0 l * C l 8) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_203 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 7 = C 0 3 + C 9 3 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 0 3) (h 2).eq
  change (∑ l : Fin 10, C 0 l * wordMatrix 2 l 3) =
    (∑ l : Fin 10, wordMatrix 2 0 l * C l 3) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_243 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 7 = C 4 3 + C 9 3 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 4 3) (h 2).eq
  change (∑ l : Fin 10, C 4 l * wordMatrix 2 l 3) =
    (∑ l : Fin 10, wordMatrix 2 4 l * C l 3) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_205 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 1 = C 0 5 + C 9 5 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 0 5) (h 2).eq
  change (∑ l : Fin 10, C 0 l * wordMatrix 2 l 5) =
    (∑ l : Fin 10, wordMatrix 2 0 l * C l 5) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_197 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 1 = C 4 7 + C 9 7 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 9 7) (h 1).eq
  change (∑ l : Fin 10, C 9 l * wordMatrix 1 l 7) =
    (∑ l : Fin 10, wordMatrix 1 9 l * C l 7) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_213 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 7 = C 5 3 + C 9 3 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 1 3) (h 2).eq
  change (∑ l : Fin 10, C 1 l * wordMatrix 2 l 3) =
    (∑ l : Fin 10, wordMatrix 2 1 l * C l 3) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_215 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 1 = C 5 5 + C 9 5 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 1 5) (h 2).eq
  change (∑ l : Fin 10, C 1 l * wordMatrix 2 l 5) =
    (∑ l : Fin 10, wordMatrix 2 1 l * C l 5) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_218 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 2 = C 5 8 + C 9 8 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 1 8) (h 2).eq
  change (∑ l : Fin 10, C 1 l * wordMatrix 2 l 8) =
    (∑ l : Fin 10, wordMatrix 2 1 l * C l 8) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_40 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 1 + C 4 2 + C 4 3 + C 4 4 + C 4 5 + C 4 6 + C 4 7 + C 4 8 + C 4 9 = C 0 0 + C 1 0 + C 2 0 + C 3 0 + C 5 0 + C 6 0 + C 7 0 + C 8 0 + C 9 0 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 4 0) (h 0).eq
  change (∑ l : Fin 10, C 4 l * wordMatrix 0 l 0) =
    (∑ l : Fin 10, wordMatrix 0 4 l * C l 0) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_90 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 1 + C 9 2 + C 9 3 + C 9 4 + C 9 5 + C 9 6 + C 9 7 + C 9 8 + C 9 9 = C 0 0 + C 1 0 + C 2 0 + C 3 0 + C 4 0 + C 5 0 + C 6 0 + C 7 0 + C 9 0 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 9 0) (h 0).eq
  change (∑ l : Fin 10, C 9 l * wordMatrix 0 l 0) =
    (∑ l : Fin 10, wordMatrix 0 9 l * C l 0) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_223 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 7 = C 8 3 + C 9 3 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 2 3) (h 2).eq
  change (∑ l : Fin 10, C 2 l * wordMatrix 2 l 3) =
    (∑ l : Fin 10, wordMatrix 2 2 l * C l 3) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_225 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 1 = C 8 5 + C 9 5 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 2 5) (h 2).eq
  change (∑ l : Fin 10, C 2 l * wordMatrix 2 l 5) =
    (∑ l : Fin 10, wordMatrix 2 2 l * C l 5) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_228 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 2 = C 8 8 + C 9 8 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 2 8) (h 2).eq
  change (∑ l : Fin 10, C 2 l * wordMatrix 2 l 8) =
    (∑ l : Fin 10, wordMatrix 2 2 l * C l 8) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_118 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 5 = C 4 8 + C 7 8 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 1 8) (h 1).eq
  change (∑ l : Fin 10, C 1 l * wordMatrix 1 l 8) =
    (∑ l : Fin 10, wordMatrix 1 1 l * C l 8) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_233 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 7 = C 7 3 + C 9 3 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 3 3) (h 2).eq
  change (∑ l : Fin 10, C 3 l * wordMatrix 2 l 3) =
    (∑ l : Fin 10, wordMatrix 2 3 l * C l 3) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_127 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 1 = C 3 7 + C 4 7 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 2 7) (h 1).eq
  change (∑ l : Fin 10, C 2 l * wordMatrix 1 l 7) =
    (∑ l : Fin 10, wordMatrix 1 2 l * C l 7) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_238 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 2 = C 7 8 + C 9 8 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 3 8) (h 2).eq
  change (∑ l : Fin 10, C 3 l * wordMatrix 2 l 8) =
    (∑ l : Fin 10, wordMatrix 2 3 l * C l 8) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_258 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 2 = C 1 8 + C 9 8 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 5 8) (h 2).eq
  change (∑ l : Fin 10, C 5 l * wordMatrix 2 l 8) =
    (∑ l : Fin 10, wordMatrix 2 5 l * C l 8) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_235 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 1 = C 7 5 + C 9 5 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 3 5) (h 2).eq
  change (∑ l : Fin 10, C 3 l * wordMatrix 2 l 5) =
    (∑ l : Fin 10, wordMatrix 2 3 l * C l 5) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_268 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 2 = C 6 8 + C 9 8 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 6 8) (h 2).eq
  change (∑ l : Fin 10, C 6 l * wordMatrix 2 l 8) =
    (∑ l : Fin 10, wordMatrix 2 6 l * C l 8) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_255 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 1 = C 1 5 + C 9 5 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 5 5) (h 2).eq
  change (∑ l : Fin 10, C 5 l * wordMatrix 2 l 5) =
    (∑ l : Fin 10, wordMatrix 2 5 l * C l 5) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_198 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 5 = C 4 8 + C 9 8 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 9 8) (h 1).eq
  change (∑ l : Fin 10, C 9 l * wordMatrix 1 l 8) =
    (∑ l : Fin 10, wordMatrix 1 9 l * C l 8) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_122 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 3 = C 3 2 + C 4 2 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 2 2) (h 1).eq
  change (∑ l : Fin 10, C 2 l * wordMatrix 1 l 2) =
    (∑ l : Fin 10, wordMatrix 1 2 l * C l 2) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_278 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 2 = C 3 8 + C 9 8 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 7 8) (h 2).eq
  change (∑ l : Fin 10, C 7 l * wordMatrix 2 l 8) =
    (∑ l : Fin 10, wordMatrix 2 7 l * C l 8) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_288 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 2 = C 2 8 + C 9 8 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 8 8) (h 2).eq
  change (∑ l : Fin 10, C 8 l * wordMatrix 2 l 8) =
    (∑ l : Fin 10, wordMatrix 2 8 l * C l 8) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_265 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 1 = C 6 5 + C 9 5 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 6 5) (h 2).eq
  change (∑ l : Fin 10, C 6 l * wordMatrix 2 l 5) =
    (∑ l : Fin 10, wordMatrix 2 6 l * C l 5) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_283 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 7 = C 2 3 + C 9 3 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 8 3) (h 2).eq
  change (∑ l : Fin 10, C 8 l * wordMatrix 2 l 3) =
    (∑ l : Fin 10, wordMatrix 2 8 l * C l 3) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_275 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 1 = C 3 5 + C 9 5 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 7 5) (h 2).eq
  change (∑ l : Fin 10, C 7 l * wordMatrix 2 l 5) =
    (∑ l : Fin 10, wordMatrix 2 7 l * C l 5) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_138 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 5 = C 2 8 + C 4 8 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 3 8) (h 1).eq
  change (∑ l : Fin 10, C 3 l * wordMatrix 1 l 8) =
    (∑ l : Fin 10, wordMatrix 1 3 l * C l 8) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_285 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 1 = C 2 5 + C 9 5 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 8 5) (h 2).eq
  change (∑ l : Fin 10, C 8 l * wordMatrix 2 l 5) =
    (∑ l : Fin 10, wordMatrix 2 8 l * C l 5) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_128 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 5 = C 3 8 + C 4 8 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 2 8) (h 1).eq
  change (∑ l : Fin 10, C 2 l * wordMatrix 1 l 8) =
    (∑ l : Fin 10, wordMatrix 1 2 l * C l 8) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_112 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 3 = C 4 2 + C 7 2 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 1 2) (h 1).eq
  change (∑ l : Fin 10, C 1 l * wordMatrix 1 l 2) =
    (∑ l : Fin 10, wordMatrix 1 1 l * C l 2) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_46 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 0 + C 4 1 + C 4 2 + C 4 3 + C 4 4 + C 4 5 + C 4 7 + C 4 8 + C 4 9 = C 0 6 + C 1 6 + C 2 6 + C 3 6 + C 5 6 + C 6 6 + C 7 6 + C 8 6 + C 9 6 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 4 6) (h 0).eq
  change (∑ l : Fin 10, C 4 l * wordMatrix 0 l 6) =
    (∑ l : Fin 10, wordMatrix 0 4 l * C l 6) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_96 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 0 + C 9 1 + C 9 2 + C 9 3 + C 9 4 + C 9 5 + C 9 7 + C 9 8 + C 9 9 = C 0 6 + C 1 6 + C 2 6 + C 3 6 + C 4 6 + C 5 6 + C 6 6 + C 7 6 + C 9 6 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 9 6) (h 0).eq
  change (∑ l : Fin 10, C 9 l * wordMatrix 0 l 6) =
    (∑ l : Fin 10, wordMatrix 0 9 l * C l 6) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_158 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 5 = C 4 8 + C 8 8 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 5 8) (h 1).eq
  change (∑ l : Fin 10, C 5 l * wordMatrix 1 l 8) =
    (∑ l : Fin 10, wordMatrix 1 5 l * C l 8) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_132 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 3 = C 2 2 + C 4 2 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 3 2) (h 1).eq
  change (∑ l : Fin 10, C 3 l * wordMatrix 1 l 2) =
    (∑ l : Fin 10, wordMatrix 1 3 l * C l 2) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_83 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 0 + C 8 1 + C 8 3 + C 8 4 + C 8 5 + C 8 6 + C 8 7 + C 8 8 + C 8 9 = C 0 3 + C 1 3 + C 2 3 + C 3 3 + C 4 3 + C 6 3 + C 7 3 + C 8 3 + C 9 3 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 8 3) (h 0).eq
  change (∑ l : Fin 10, C 8 l * wordMatrix 0 l 3) =
    (∑ l : Fin 10, wordMatrix 0 8 l * C l 3) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_187 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 1 = C 4 7 + C 5 7 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 8 7) (h 1).eq
  change (∑ l : Fin 10, C 8 l * wordMatrix 1 l 7) =
    (∑ l : Fin 10, wordMatrix 1 8 l * C l 7) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_168 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 5 = C 4 8 + C 6 8 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 6 8) (h 1).eq
  change (∑ l : Fin 10, C 6 l * wordMatrix 1 l 8) =
    (∑ l : Fin 10, wordMatrix 1 6 l * C l 8) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_162 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 3 = C 4 2 + C 6 2 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 6 2) (h 1).eq
  change (∑ l : Fin 10, C 6 l * wordMatrix 1 l 2) =
    (∑ l : Fin 10, wordMatrix 1 6 l * C l 2) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_263 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 7 = C 6 3 + C 9 3 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 6 3) (h 2).eq
  change (∑ l : Fin 10, C 6 l * wordMatrix 2 l 3) =
    (∑ l : Fin 10, wordMatrix 2 6 l * C l 3) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_192 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 3 = C 4 2 + C 9 2 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 9 2) (h 1).eq
  change (∑ l : Fin 10, C 9 l * wordMatrix 1 l 2) =
    (∑ l : Fin 10, wordMatrix 1 9 l * C l 2) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_273 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 7 = C 3 3 + C 9 3 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 7 3) (h 2).eq
  change (∑ l : Fin 10, C 7 l * wordMatrix 2 l 3) =
    (∑ l : Fin 10, wordMatrix 2 7 l * C l 3) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_152 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 3 = C 4 2 + C 8 2 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 5 2) (h 1).eq
  change (∑ l : Fin 10, C 5 l * wordMatrix 1 l 2) =
    (∑ l : Fin 10, wordMatrix 1 5 l * C l 2) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_182 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 3 = C 4 2 + C 5 2 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 8 2) (h 1).eq
  change (∑ l : Fin 10, C 8 l * wordMatrix 1 l 2) =
    (∑ l : Fin 10, wordMatrix 1 8 l * C l 2) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_172 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 3 = C 1 2 + C 4 2 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 7 2) (h 1).eq
  change (∑ l : Fin 10, C 7 l * wordMatrix 1 l 2) =
    (∑ l : Fin 10, wordMatrix 1 7 l * C l 2) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_28 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 0 + C 2 1 + C 2 2 + C 2 3 + C 2 4 + C 2 5 + C 2 6 + C 2 7 + C 2 8 = C 0 8 + C 1 8 + C 2 8 + C 4 8 + C 5 8 + C 6 8 + C 7 8 + C 8 8 + C 9 8 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 2 8) (h 0).eq
  change (∑ l : Fin 10, C 2 l * wordMatrix 0 l 8) =
    (∑ l : Fin 10, wordMatrix 0 2 l * C l 8) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_88 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 0 + C 8 1 + C 8 2 + C 8 3 + C 8 4 + C 8 5 + C 8 6 + C 8 7 + C 8 8 = C 0 8 + C 1 8 + C 2 8 + C 3 8 + C 4 8 + C 6 8 + C 7 8 + C 8 8 + C 9 8 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 8 8) (h 0).eq
  change (∑ l : Fin 10, C 8 l * wordMatrix 0 l 8) =
    (∑ l : Fin 10, wordMatrix 0 8 l * C l 8) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_87 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 0 + C 8 1 + C 8 2 + C 8 3 + C 8 4 + C 8 5 + C 8 6 + C 8 8 + C 8 9 = C 0 7 + C 1 7 + C 2 7 + C 3 7 + C 4 7 + C 6 7 + C 7 7 + C 8 7 + C 9 7 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 8 7) (h 0).eq
  change (∑ l : Fin 10, C 8 l * wordMatrix 0 l 7) =
    (∑ l : Fin 10, wordMatrix 0 8 l * C l 7) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_81 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 0 + C 8 1 + C 8 2 + C 8 3 + C 8 4 + C 8 6 + C 8 7 + C 8 8 + C 8 9 = C 0 1 + C 1 1 + C 2 1 + C 3 1 + C 4 1 + C 6 1 + C 7 1 + C 8 1 + C 9 1 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 8 1) (h 0).eq
  change (∑ l : Fin 10, C 8 l * wordMatrix 0 l 1) =
    (∑ l : Fin 10, wordMatrix 0 8 l * C l 1) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_178 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 5 = C 1 8 + C 4 8 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 7 8) (h 1).eq
  change (∑ l : Fin 10, C 7 l * wordMatrix 1 l 8) =
    (∑ l : Fin 10, wordMatrix 1 7 l * C l 8) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_55 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 0 + C 5 1 + C 5 2 + C 5 3 + C 5 4 + C 5 5 + C 5 6 + C 5 7 + C 5 9 = C 0 5 + C 2 5 + C 3 5 + C 4 5 + C 5 5 + C 6 5 + C 7 5 + C 8 5 + C 9 5 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 5 5) (h 0).eq
  change (∑ l : Fin 10, C 5 l * wordMatrix 0 l 5) =
    (∑ l : Fin 10, wordMatrix 0 5 l * C l 5) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_52 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 0 + C 5 1 + C 5 2 + C 5 3 + C 5 4 + C 5 5 + C 5 6 + C 5 7 + C 5 8 + C 5 9 = C 0 2 + C 2 2 + C 3 2 + C 4 2 + C 5 2 + C 6 2 + C 7 2 + C 8 2 + C 9 2 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 5 2) (h 0).eq
  change (∑ l : Fin 10, C 5 l * wordMatrix 0 l 2) =
    (∑ l : Fin 10, wordMatrix 0 5 l * C l 2) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_85 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 0 + C 8 1 + C 8 2 + C 8 3 + C 8 4 + C 8 5 + C 8 6 + C 8 7 + C 8 9 = C 0 5 + C 1 5 + C 2 5 + C 3 5 + C 4 5 + C 6 5 + C 7 5 + C 8 5 + C 9 5 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 8 5) (h 0).eq
  change (∑ l : Fin 10, C 8 l * wordMatrix 0 l 5) =
    (∑ l : Fin 10, wordMatrix 0 8 l * C l 5) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_82 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 0 + C 8 1 + C 8 2 + C 8 3 + C 8 4 + C 8 5 + C 8 6 + C 8 7 + C 8 8 + C 8 9 = C 0 2 + C 1 2 + C 2 2 + C 3 2 + C 4 2 + C 6 2 + C 7 2 + C 8 2 + C 9 2 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 8 2) (h 0).eq
  change (∑ l : Fin 10, C 8 l * wordMatrix 0 l 2) =
    (∑ l : Fin 10, wordMatrix 0 8 l * C l 2) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_22 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 0 + C 2 1 + C 2 2 + C 2 3 + C 2 4 + C 2 5 + C 2 6 + C 2 7 + C 2 8 + C 2 9 = C 0 2 + C 1 2 + C 2 2 + C 4 2 + C 5 2 + C 6 2 + C 7 2 + C 8 2 + C 9 2 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 2 2) (h 0).eq
  change (∑ l : Fin 10, C 2 l * wordMatrix 0 l 2) =
    (∑ l : Fin 10, wordMatrix 0 2 l * C l 2) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_35 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 0 + C 3 1 + C 3 2 + C 3 3 + C 3 4 + C 3 5 + C 3 6 + C 3 7 + C 3 9 = C 0 5 + C 1 5 + C 2 5 + C 3 5 + C 4 5 + C 5 5 + C 6 5 + C 7 5 + C 8 5 + C 9 5 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 3 5) (h 0).eq
  change (∑ l : Fin 10, C 3 l * wordMatrix 0 l 5) =
    (∑ l : Fin 10, wordMatrix 0 3 l * C l 5) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_75 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 0 + C 7 1 + C 7 2 + C 7 3 + C 7 4 + C 7 5 + C 7 6 + C 7 7 + C 7 9 = C 0 5 + C 1 5 + C 2 5 + C 3 5 + C 4 5 + C 5 5 + C 6 5 + C 8 5 + C 9 5 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 7 5) (h 0).eq
  change (∑ l : Fin 10, C 7 l * wordMatrix 0 l 5) =
    (∑ l : Fin 10, wordMatrix 0 7 l * C l 5) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_57 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 0 + C 5 1 + C 5 2 + C 5 3 + C 5 4 + C 5 5 + C 5 6 + C 5 8 + C 5 9 = C 0 7 + C 2 7 + C 3 7 + C 4 7 + C 5 7 + C 6 7 + C 7 7 + C 8 7 + C 9 7 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 5 7) (h 0).eq
  change (∑ l : Fin 10, C 5 l * wordMatrix 0 l 7) =
    (∑ l : Fin 10, wordMatrix 0 5 l * C l 7) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_49 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 0 + C 4 2 + C 4 3 + C 4 4 + C 4 5 + C 4 6 + C 4 7 + C 4 8 + C 4 9 = C 0 9 + C 1 9 + C 2 9 + C 3 9 + C 5 9 + C 6 9 + C 7 9 + C 8 9 + C 9 9 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 4 9) (h 0).eq
  change (∑ l : Fin 10, C 4 l * wordMatrix 0 l 9) =
    (∑ l : Fin 10, wordMatrix 0 4 l * C l 9) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_269 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 0 + C 6 1 + C 6 2 + C 6 3 + C 6 4 + C 6 5 + C 6 6 + C 6 7 + C 6 8 + C 6 9 = C 6 9 + C 9 9 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 6 9) (h 2).eq
  change (∑ l : Fin 10, C 6 l * wordMatrix 2 l 9) =
    (∑ l : Fin 10, wordMatrix 2 6 l * C l 9) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_60 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 1 + C 6 2 + C 6 3 + C 6 4 + C 6 5 + C 6 6 + C 6 7 + C 6 8 + C 6 9 = C 0 0 + C 1 0 + C 2 0 + C 3 0 + C 4 0 + C 5 0 + C 7 0 + C 8 0 + C 9 0 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 6 0) (h 0).eq
  change (∑ l : Fin 10, C 6 l * wordMatrix 0 l 0) =
    (∑ l : Fin 10, wordMatrix 0 6 l * C l 0) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_164 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 0 + C 6 1 + C 6 2 + C 6 3 + C 6 4 + C 6 5 + C 6 6 + C 6 7 + C 6 8 + C 6 9 = C 4 4 + C 6 4 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 6 4) (h 1).eq
  change (∑ l : Fin 10, C 6 l * wordMatrix 1 l 4) =
    (∑ l : Fin 10, wordMatrix 1 6 l * C l 4) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_69 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 0 + C 6 2 + C 6 3 + C 6 4 + C 6 5 + C 6 6 + C 6 7 + C 6 8 + C 6 9 = C 0 9 + C 1 9 + C 2 9 + C 3 9 + C 4 9 + C 5 9 + C 7 9 + C 8 9 + C 9 9 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 6 9) (h 0).eq
  change (∑ l : Fin 10, C 6 l * wordMatrix 0 l 9) =
    (∑ l : Fin 10, wordMatrix 0 6 l * C l 9) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem equation_3 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 0 + C 0 1 + C 0 3 + C 0 4 + C 0 5 + C 0 6 + C 0 7 + C 0 8 + C 0 9 = C 1 3 + C 2 3 + C 3 3 + C 4 3 + C 5 3 + C 6 3 + C 7 3 + C 8 3 + C 9 3 := by
  have he := congrArg (fun M : Matrix (Fin 10) (Fin 10) (ZMod 2) => M 0 3) (h 0).eq
  change (∑ l : Fin 10, C 0 l * wordMatrix 0 l 3) =
    (∑ l : Fin 10, wordMatrix 0 0 l * C l 3) at he
  simpa [Fin.sum_univ_succ, wordMatrix, wordSupport, add_assoc] using he

private theorem pivot_40 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_100 C h

private theorem pivot_46 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_106 C h

private theorem pivot_49 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_109 C h

private theorem pivot_90 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_200 C h

private theorem pivot_94 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_204 C h

private theorem pivot_96 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_206 C h

private theorem pivot_41 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 1 = C 4 7 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_141 C h

private theorem pivot_43 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 3 = C 4 2 := by
  linear_combination (norm := ring_nf)
    equation_142 C h

private theorem pivot_45 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 5 = C 4 8 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_145 C h

private theorem pivot_91 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 1 = C 9 5 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_291 C h

private theorem pivot_92 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 2 = C 9 8 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_292 C h

private theorem pivot_97 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 7 = C 9 3 := by
  linear_combination (norm := ring_nf)
    equation_293 C h

private theorem pivot_10 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 0 = C 7 0 := by
  linear_combination (norm := ring_nf)
    equation_110 C h + pivot_40 C h

private theorem pivot_16 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 6 = C 7 6 := by
  linear_combination (norm := ring_nf)
    equation_116 C h + pivot_46 C h

private theorem pivot_79 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 9 = C 1 9 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_119 C h + pivot_49 C h

private theorem pivot_20 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 0 = C 3 0 := by
  linear_combination (norm := ring_nf)
    equation_120 C h + pivot_40 C h

private theorem pivot_26 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 6 = C 3 6 := by
  linear_combination (norm := ring_nf)
    equation_126 C h + pivot_46 C h

private theorem pivot_29 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 9 = C 3 9 := by
  linear_combination (norm := ring_nf)
    equation_129 C h + pivot_49 C h

private theorem pivot_50 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 0 = C 8 0 := by
  linear_combination (norm := ring_nf)
    equation_150 C h + pivot_40 C h

private theorem pivot_56 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 6 = C 8 6 := by
  linear_combination (norm := ring_nf)
    equation_156 C h + pivot_46 C h

private theorem pivot_59 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 9 = C 8 9 := by
  linear_combination (norm := ring_nf)
    equation_159 C h + pivot_49 C h

private theorem pivot_14 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 4 = C 5 4 := by
  linear_combination (norm := ring_nf)
    equation_214 C h + pivot_94 C h

private theorem pivot_24 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 4 = C 8 4 := by
  linear_combination (norm := ring_nf)
    equation_224 C h + pivot_94 C h

private theorem pivot_70 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 0 = C 3 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_230 C h + pivot_90 C h

private theorem pivot_34 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 4 = C 7 4 := by
  linear_combination (norm := ring_nf)
    equation_234 C h + pivot_94 C h

private theorem pivot_76 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 6 = C 3 6 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_236 C h + pivot_96 C h

private theorem pivot_30 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 0 = C 8 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_220 C h + pivot_90 C h + pivot_20 C h

private theorem pivot_36 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 6 = C 8 6 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_226 C h + pivot_96 C h + pivot_26 C h

private theorem pivot_44 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 4 = C 9 9 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_194 C h + pivot_90 C h + pivot_96 C h + pivot_91 C h + pivot_92 C h + pivot_97 C h

private theorem pivot_4 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 4 = C 6 4 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_44 C h + pivot_40 C h + pivot_46 C h + pivot_49 C h + pivot_94 C h + pivot_41 C h + pivot_43 C h + pivot_45 C h + pivot_14 C h + pivot_24 C h + pivot_34 C h

private theorem pivot_84 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_94 C h + pivot_90 C h + pivot_94 C h + pivot_96 C h + pivot_91 C h + pivot_92 C h + pivot_97 C h + pivot_14 C h + pivot_24 C h + pivot_34 C h + pivot_44 C h + pivot_4 C h

private theorem pivot_42 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 2 = C 0 2 + C 0 3 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_102 C h

private theorem pivot_47 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 7 = C 0 1 + C 0 7 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_107 C h

private theorem pivot_48 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 8 = C 0 5 + C 0 8 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_108 C h

private theorem pivot_7 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 7 = C 0 3 + C 9 3 := by
  linear_combination (norm := ring_nf)
    equation_203 C h

private theorem pivot_2 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 2 = C 0 1 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_243 C h + pivot_43 C h + pivot_42 C h + pivot_47 C h + pivot_7 C h

private theorem pivot_1 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 1 = C 0 5 + C 9 5 := by
  linear_combination (norm := ring_nf)
    equation_205 C h

private theorem pivot_5 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 5 = C 0 3 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_197 C h + pivot_91 C h + pivot_97 C h + pivot_47 C h + pivot_7 C h + pivot_1 C h

private theorem pivot_93 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 3 = C 1 7 + C 5 3 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_213 C h

private theorem pivot_95 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 5 = C 1 1 + C 5 5 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_215 C h

private theorem pivot_98 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 8 = C 1 2 + C 5 8 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_218 C h

private theorem pivot_99 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 9 = C 0 0 + C 6 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_40 C h + pivot_46 C h + pivot_49 C h + pivot_90 C h + pivot_41 C h + pivot_43 C h + pivot_45 C h + pivot_10 C h + pivot_20 C h + pivot_50 C h + pivot_44 C h

private theorem pivot_80 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_90 C h + pivot_40 C h + pivot_90 C h + pivot_94 C h + pivot_96 C h + pivot_91 C h + pivot_92 C h + pivot_97 C h + pivot_10 C h + pivot_20 C h + pivot_50 C h + pivot_99 C h

private theorem pivot_53 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 3 = C 1 7 + C 2 7 + C 8 3 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_223 C h + pivot_93 C h

private theorem pivot_11 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 1 = C 2 1 + C 5 5 + C 8 5 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_225 C h + pivot_95 C h

private theorem pivot_12 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 2 = C 2 2 + C 5 8 + C 8 8 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_228 C h + pivot_98 C h

private theorem pivot_3 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 3 = C 0 8 + C 1 5 + C 7 8 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_118 C h + pivot_48 C h + pivot_5 C h

private theorem pivot_83 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 3 = C 2 7 + C 3 7 + C 7 3 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_233 C h + pivot_93 C h + pivot_53 C h

private theorem pivot_85 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 5 = C 7 3 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_127 C h + pivot_47 C h + pivot_7 C h + pivot_1 C h + pivot_5 C h + pivot_93 C h + pivot_95 C h + pivot_53 C h + pivot_11 C h + pivot_83 C h

private theorem pivot_78 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 8 = C 2 2 + C 3 2 + C 8 8 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_238 C h + pivot_98 C h + pivot_12 C h

private theorem pivot_22 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 2 = C 1 8 + C 5 2 + C 8 8 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_258 C h + pivot_98 C h + pivot_12 C h

private theorem pivot_73 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 3 = C 2 1 + C 3 1 + C 7 5 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_235 C h + pivot_95 C h + pivot_11 C h + pivot_85 C h

private theorem pivot_52 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 2 = C 1 8 + C 6 2 + C 6 8 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_268 C h + pivot_98 C h + pivot_12 C h + pivot_22 C h

private theorem pivot_31 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 1 = C 1 5 + C 5 1 + C 7 5 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_255 C h + pivot_95 C h + pivot_11 C h + pivot_85 C h + pivot_73 C h

private theorem pivot_51 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 1 = C 3 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_198 C h + pivot_48 C h + pivot_5 C h + pivot_95 C h + pivot_98 C h + pivot_11 C h + pivot_12 C h + pivot_3 C h + pivot_85 C h + pivot_78 C h + pivot_73 C h + pivot_31 C h

private theorem pivot_15 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 5 = C 2 3 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_122 C h + pivot_42 C h + pivot_2 C h + pivot_1 C h + pivot_5 C h + pivot_95 C h + pivot_11 C h + pivot_85 C h + pivot_73 C h + pivot_31 C h + pivot_51 C h

private theorem pivot_62 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 2 = C 3 8 + C 6 8 + C 7 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_278 C h + pivot_98 C h + pivot_12 C h + pivot_22 C h + pivot_52 C h

private theorem pivot_38 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 8 = C 2 8 + C 7 2 + C 8 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_288 C h + pivot_98 C h + pivot_12 C h + pivot_22 C h + pivot_52 C h + pivot_62 C h

private theorem pivot_23 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 3 = C 3 2 + C 6 1 + C 6 5 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_265 C h + pivot_95 C h + pivot_11 C h + pivot_85 C h + pivot_73 C h + pivot_31 C h + pivot_51 C h + pivot_15 C h

private theorem pivot_21 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 1 = C 3 2 + C 3 7 + C 8 7 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_283 C h + pivot_93 C h + pivot_53 C h + pivot_83 C h + pivot_73 C h + pivot_31 C h + pivot_51 C h + pivot_15 C h

private theorem pivot_61 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 1 = C 3 5 + C 6 5 + C 7 1 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_275 C h + pivot_95 C h + pivot_11 C h + pivot_85 C h + pivot_73 C h + pivot_31 C h + pivot_51 C h + pivot_15 C h + pivot_23 C h

private theorem pivot_82 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 2 = C 7 1 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_138 C h + pivot_48 C h + pivot_5 C h + pivot_3 C h + pivot_78 C h + pivot_22 C h + pivot_52 C h + pivot_15 C h + pivot_62 C h + pivot_38 C h + pivot_23 C h + pivot_61 C h

private theorem pivot_71 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 1 = C 2 5 + C 3 5 + C 8 1 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_285 C h + pivot_95 C h + pivot_11 C h + pivot_85 C h + pivot_73 C h + pivot_31 C h + pivot_51 C h + pivot_15 C h + pivot_23 C h + pivot_61 C h

private theorem pivot_81 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 1 = C 7 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_128 C h + pivot_48 C h + pivot_5 C h + pivot_3 C h + pivot_78 C h + pivot_22 C h + pivot_52 C h + pivot_15 C h + pivot_62 C h + pivot_23 C h + pivot_61 C h + pivot_71 C h

private theorem pivot_25 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 5 = C 1 3 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_112 C h + pivot_42 C h + pivot_2 C h + pivot_1 C h + pivot_5 C h + pivot_95 C h + pivot_11 C h + pivot_85 C h + pivot_73 C h + pivot_31 C h + pivot_51 C h + pivot_15 C h + pivot_23 C h + pivot_61 C h + pivot_71 C h + pivot_81 C h

private theorem pivot_60 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 0 = C 0 0 + C 0 6 + C 6 6 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_46 C h + pivot_40 C h + pivot_49 C h + pivot_96 C h + pivot_41 C h + pivot_43 C h + pivot_45 C h + pivot_16 C h + pivot_26 C h + pivot_56 C h + pivot_44 C h + pivot_99 C h

private theorem pivot_86 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_96 C h + pivot_46 C h + pivot_90 C h + pivot_94 C h + pivot_96 C h + pivot_91 C h + pivot_92 C h + pivot_97 C h + pivot_16 C h + pivot_26 C h + pivot_56 C h + pivot_99 C h + pivot_60 C h

private theorem pivot_35 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 5 = C 2 8 + C 5 5 + C 8 8 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_158 C h + pivot_48 C h + pivot_5 C h + pivot_3 C h + pivot_78 C h + pivot_22 C h + pivot_52 C h + pivot_15 C h + pivot_62 C h + pivot_38 C h + pivot_23 C h + pivot_61 C h + pivot_82 C h

private theorem pivot_55 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 5 = C 3 3 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_132 C h + pivot_42 C h + pivot_2 C h + pivot_1 C h + pivot_5 C h + pivot_95 C h + pivot_11 C h + pivot_85 C h + pivot_22 C h + pivot_73 C h + pivot_52 C h + pivot_31 C h + pivot_51 C h + pivot_15 C h + pivot_62 C h + pivot_38 C h + pivot_23 C h + pivot_61 C h + pivot_82 C h + pivot_35 C h

private theorem pivot_8 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 8 = C 6 3 + C 8 9 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_83 C h + pivot_43 C h + pivot_84 C h + pivot_42 C h + pivot_2 C h + pivot_1 C h + pivot_5 C h + pivot_93 C h + pivot_95 C h + pivot_80 C h + pivot_53 C h + pivot_11 C h + pivot_3 C h + pivot_83 C h + pivot_78 C h + pivot_22 C h + pivot_52 C h + pivot_15 C h + pivot_62 C h + pivot_38 C h + pivot_21 C h + pivot_82 C h + pivot_71 C h + pivot_25 C h + pivot_86 C h + pivot_35 C h + pivot_55 C h

private theorem pivot_32 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 2 = C 5 7 + C 7 2 + C 8 7 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_187 C h + pivot_47 C h + pivot_7 C h + pivot_1 C h + pivot_5 C h + pivot_93 C h + pivot_95 C h + pivot_53 C h + pivot_11 C h + pivot_83 C h + pivot_85 C h + pivot_21 C h + pivot_81 C h

private theorem pivot_33 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 3 = C 6 5 + C 6 8 + C 8 8 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_168 C h + pivot_48 C h + pivot_5 C h + pivot_3 C h + pivot_78 C h + pivot_22 C h + pivot_52 C h + pivot_15 C h + pivot_62 C h + pivot_38 C h + pivot_23 C h + pivot_61 C h + pivot_82 C h + pivot_35 C h + pivot_55 C h

private theorem pivot_65 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 5 = C 6 3 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_162 C h + pivot_42 C h + pivot_2 C h + pivot_1 C h + pivot_5 C h + pivot_95 C h + pivot_11 C h + pivot_85 C h + pivot_73 C h + pivot_31 C h + pivot_51 C h + pivot_15 C h + pivot_62 C h + pivot_38 C h + pivot_23 C h + pivot_61 C h + pivot_82 C h + pivot_35 C h + pivot_55 C h + pivot_33 C h

private theorem pivot_13 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 3 = C 5 7 + C 6 3 + C 6 7 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_263 C h + pivot_93 C h + pivot_53 C h + pivot_83 C h + pivot_73 C h + pivot_31 C h + pivot_51 C h + pivot_15 C h + pivot_23 C h + pivot_21 C h + pivot_61 C h + pivot_71 C h + pivot_81 C h + pivot_25 C h + pivot_32 C h

private theorem pivot_67 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 7 = C 6 8 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_192 C h + pivot_92 C h + pivot_42 C h + pivot_2 C h + pivot_1 C h + pivot_5 C h + pivot_93 C h + pivot_95 C h + pivot_98 C h + pivot_53 C h + pivot_11 C h + pivot_12 C h + pivot_83 C h + pivot_85 C h + pivot_22 C h + pivot_52 C h + pivot_62 C h + pivot_38 C h + pivot_21 C h + pivot_82 C h + pivot_71 C h + pivot_81 C h + pivot_25 C h + pivot_35 C h + pivot_55 C h + pivot_32 C h + pivot_33 C h + pivot_65 C h + pivot_13 C h

private theorem pivot_88 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 8 = C 7 7 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_273 C h + pivot_93 C h + pivot_53 C h + pivot_83 C h + pivot_73 C h + pivot_31 C h + pivot_51 C h + pivot_15 C h + pivot_23 C h + pivot_21 C h + pivot_61 C h + pivot_71 C h + pivot_81 C h + pivot_25 C h + pivot_32 C h + pivot_33 C h + pivot_65 C h + pivot_13 C h + pivot_67 C h

private theorem pivot_28 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 8 = C 1 7 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_152 C h + pivot_42 C h + pivot_2 C h + pivot_1 C h + pivot_5 C h + pivot_95 C h + pivot_53 C h + pivot_11 C h + pivot_83 C h + pivot_85 C h + pivot_21 C h + pivot_82 C h + pivot_71 C h + pivot_81 C h + pivot_25 C h + pivot_35 C h + pivot_55 C h + pivot_32 C h + pivot_33 C h + pivot_65 C h + pivot_13 C h + pivot_67 C h

private theorem pivot_27 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 7 = C 1 8 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_182 C h + pivot_42 C h + pivot_2 C h + pivot_1 C h + pivot_5 C h + pivot_95 C h + pivot_11 C h + pivot_83 C h + pivot_85 C h + pivot_52 C h + pivot_62 C h + pivot_38 C h + pivot_21 C h + pivot_82 C h + pivot_71 C h + pivot_81 C h + pivot_25 C h + pivot_35 C h + pivot_55 C h + pivot_32 C h + pivot_33 C h + pivot_65 C h + pivot_13 C h + pivot_67 C h

private theorem pivot_37 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 7 = C 5 8 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_172 C h + pivot_42 C h + pivot_2 C h + pivot_1 C h + pivot_5 C h + pivot_95 C h + pivot_11 C h + pivot_12 C h + pivot_85 C h + pivot_22 C h + pivot_52 C h + pivot_62 C h + pivot_38 C h + pivot_21 C h + pivot_82 C h + pivot_71 C h + pivot_81 C h + pivot_25 C h + pivot_35 C h + pivot_55 C h + pivot_32 C h + pivot_33 C h + pivot_65 C h + pivot_13 C h + pivot_67 C h

private theorem pivot_89 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 9 = C 7 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_28 C h + pivot_20 C h + pivot_26 C h + pivot_24 C h + pivot_30 C h + pivot_36 C h + pivot_84 C h + pivot_48 C h + pivot_5 C h + pivot_98 C h + pivot_80 C h + pivot_12 C h + pivot_3 C h + pivot_15 C h + pivot_21 C h + pivot_25 C h + pivot_86 C h + pivot_8 C h + pivot_32 C h + pivot_13 C h + pivot_67 C h + pivot_27 C h + pivot_37 C h

private theorem pivot_58 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 8 = C 5 7 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_88 C h + pivot_84 C h + pivot_48 C h + pivot_5 C h + pivot_98 C h + pivot_80 C h + pivot_12 C h + pivot_3 C h + pivot_83 C h + pivot_85 C h + pivot_22 C h + pivot_52 C h + pivot_15 C h + pivot_62 C h + pivot_23 C h + pivot_61 C h + pivot_82 C h + pivot_81 C h + pivot_86 C h + pivot_35 C h + pivot_55 C h + pivot_8 C h + pivot_32 C h + pivot_33 C h + pivot_65 C h + pivot_27 C h + pivot_37 C h + pivot_89 C h

private theorem pivot_87 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 7 = C 7 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_87 C h + pivot_97 C h + pivot_84 C h + pivot_47 C h + pivot_1 C h + pivot_5 C h + pivot_93 C h + pivot_95 C h + pivot_80 C h + pivot_53 C h + pivot_11 C h + pivot_3 C h + pivot_78 C h + pivot_22 C h + pivot_52 C h + pivot_15 C h + pivot_62 C h + pivot_38 C h + pivot_23 C h + pivot_21 C h + pivot_61 C h + pivot_71 C h + pivot_25 C h + pivot_86 C h + pivot_8 C h + pivot_32 C h + pivot_13 C h + pivot_88 C h + pivot_28 C h

private theorem pivot_18 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 8 = C 7 5 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_81 C h + pivot_41 C h + pivot_91 C h + pivot_84 C h + pivot_47 C h + pivot_7 C h + pivot_93 C h + pivot_95 C h + pivot_80 C h + pivot_53 C h + pivot_3 C h + pivot_78 C h + pivot_22 C h + pivot_52 C h + pivot_31 C h + pivot_51 C h + pivot_62 C h + pivot_38 C h + pivot_21 C h + pivot_61 C h + pivot_86 C h + pivot_35 C h + pivot_8 C h + pivot_32 C h + pivot_65 C h + pivot_27 C h + pivot_37 C h + pivot_58 C h + pivot_87 C h

private theorem pivot_63 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 3 = C 6 8 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_178 C h + pivot_48 C h + pivot_5 C h + pivot_3 C h + pivot_78 C h + pivot_22 C h + pivot_52 C h + pivot_15 C h + pivot_62 C h + pivot_38 C h + pivot_23 C h + pivot_61 C h + pivot_82 C h + pivot_35 C h + pivot_55 C h + pivot_33 C h + pivot_65 C h + pivot_18 C h

private theorem pivot_54 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_55 C h + pivot_45 C h + pivot_50 C h + pivot_56 C h + pivot_59 C h + pivot_48 C h + pivot_95 C h + pivot_80 C h + pivot_53 C h + pivot_11 C h + pivot_83 C h + pivot_73 C h + pivot_52 C h + pivot_31 C h + pivot_15 C h + pivot_62 C h + pivot_38 C h + pivot_23 C h + pivot_61 C h + pivot_82 C h + pivot_25 C h + pivot_86 C h + pivot_8 C h + pivot_32 C h + pivot_65 C h + pivot_13 C h + pivot_67 C h + pivot_28 C h + pivot_37 C h + pivot_58 C h + pivot_87 C h + pivot_18 C h + pivot_63 C h

private theorem pivot_72 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_52 C h + pivot_92 C h + pivot_50 C h + pivot_56 C h + pivot_59 C h + pivot_42 C h + pivot_98 C h + pivot_80 C h + pivot_53 C h + pivot_12 C h + pivot_3 C h + pivot_83 C h + pivot_78 C h + pivot_22 C h + pivot_73 C h + pivot_52 C h + pivot_31 C h + pivot_21 C h + pivot_82 C h + pivot_71 C h + pivot_81 C h + pivot_25 C h + pivot_86 C h + pivot_35 C h + pivot_8 C h + pivot_32 C h + pivot_13 C h + pivot_67 C h + pivot_28 C h + pivot_58 C h + pivot_54 C h

private theorem pivot_57 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_85 C h + pivot_45 C h + pivot_84 C h + pivot_48 C h + pivot_95 C h + pivot_80 C h + pivot_11 C h + pivot_83 C h + pivot_85 C h + pivot_15 C h + pivot_23 C h + pivot_21 C h + pivot_61 C h + pivot_82 C h + pivot_81 C h + pivot_25 C h + pivot_86 C h + pivot_8 C h + pivot_65 C h + pivot_13 C h + pivot_67 C h + pivot_27 C h + pivot_18 C h + pivot_63 C h + pivot_72 C h

private theorem pivot_75 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_82 C h + pivot_92 C h + pivot_84 C h + pivot_42 C h + pivot_98 C h + pivot_80 C h + pivot_3 C h + pivot_83 C h + pivot_85 C h + pivot_78 C h + pivot_15 C h + pivot_62 C h + pivot_38 C h + pivot_23 C h + pivot_61 C h + pivot_82 C h + pivot_81 C h + pivot_86 C h + pivot_35 C h + pivot_55 C h + pivot_8 C h + pivot_32 C h + pivot_33 C h + pivot_65 C h + pivot_27 C h + pivot_37 C h + pivot_18 C h + pivot_72 C h + pivot_57 C h

private theorem pivot_39 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_22 C h + pivot_92 C h + pivot_20 C h + pivot_26 C h + pivot_29 C h + pivot_24 C h + pivot_30 C h + pivot_36 C h + pivot_84 C h + pivot_42 C h + pivot_98 C h + pivot_80 C h + pivot_3 C h + pivot_78 C h + pivot_22 C h + pivot_15 C h + pivot_62 C h + pivot_38 C h + pivot_21 C h + pivot_25 C h + pivot_86 C h + pivot_8 C h + pivot_13 C h + pivot_67 C h + pivot_27 C h + pivot_37 C h + pivot_89 C h + pivot_87 C h + pivot_72 C h + pivot_57 C h

private theorem pivot_74 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_35 C h + pivot_45 C h + pivot_34 C h + pivot_30 C h + pivot_36 C h + pivot_48 C h + pivot_95 C h + pivot_80 C h + pivot_11 C h + pivot_31 C h + pivot_51 C h + pivot_21 C h + pivot_25 C h + pivot_86 C h + pivot_55 C h + pivot_8 C h + pivot_32 C h + pivot_65 C h + pivot_13 C h + pivot_67 C h + pivot_89 C h + pivot_63 C h + pivot_39 C h

private theorem pivot_19 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_75 C h + pivot_45 C h + pivot_79 C h + pivot_70 C h + pivot_76 C h + pivot_30 C h + pivot_36 C h + pivot_48 C h + pivot_95 C h + pivot_80 C h + pivot_11 C h + pivot_73 C h + pivot_31 C h + pivot_51 C h + pivot_71 C h + pivot_81 C h + pivot_86 C h + pivot_55 C h + pivot_8 C h + pivot_32 C h + pivot_33 C h + pivot_88 C h + pivot_89 C h + pivot_87 C h + pivot_63 C h + pivot_72 C h + pivot_57 C h + pivot_75 C h + pivot_74 C h

private theorem pivot_17 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_57 C h + pivot_97 C h + pivot_50 C h + pivot_56 C h + pivot_59 C h + pivot_47 C h + pivot_1 C h + pivot_5 C h + pivot_93 C h + pivot_95 C h + pivot_80 C h + pivot_11 C h + pivot_3 C h + pivot_85 C h + pivot_78 C h + pivot_22 C h + pivot_73 C h + pivot_31 C h + pivot_86 C h + pivot_55 C h + pivot_8 C h + pivot_32 C h + pivot_33 C h + pivot_65 C h + pivot_67 C h + pivot_88 C h + pivot_27 C h + pivot_37 C h + pivot_54 C h + pivot_72 C h

private theorem pivot_9 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 9 = C 6 9 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_49 C h + pivot_40 C h + pivot_46 C h + pivot_49 C h + pivot_43 C h + pivot_45 C h + pivot_79 C h + pivot_29 C h + pivot_59 C h + pivot_44 C h + pivot_47 C h + pivot_7 C h + pivot_1 C h + pivot_5 C h + pivot_93 C h + pivot_95 C h + pivot_53 C h + pivot_11 C h + pivot_83 C h + pivot_85 C h + pivot_21 C h + pivot_32 C h + pivot_72 C h + pivot_57 C h

private theorem pivot_66 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 6 = C 0 0 + C 6 4 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_269 C h + pivot_99 C h + pivot_62 C h + pivot_38 C h + pivot_61 C h + pivot_82 C h + pivot_35 C h + pivot_55 C h + pivot_33 C h + pivot_65 C h + pivot_67 C h

private theorem pivot_69 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_60 C h + pivot_40 C h + pivot_90 C h + pivot_10 C h + pivot_20 C h + pivot_50 C h + pivot_62 C h + pivot_38 C h + pivot_61 C h + pivot_82 C h + pivot_35 C h + pivot_55 C h + pivot_33 C h + pivot_65 C h + pivot_67 C h + pivot_66 C h

private theorem pivot_64 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_164 C h + pivot_44 C h + pivot_99 C h + pivot_62 C h + pivot_38 C h + pivot_61 C h + pivot_82 C h + pivot_35 C h + pivot_55 C h + pivot_33 C h + pivot_65 C h + pivot_67 C h + pivot_66 C h + pivot_69 C h

private theorem pivot_68 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_69 C h + pivot_49 C h + pivot_79 C h + pivot_29 C h + pivot_59 C h + pivot_99 C h + pivot_62 C h + pivot_38 C h + pivot_82 C h + pivot_71 C h + pivot_81 C h + pivot_25 C h + pivot_35 C h + pivot_55 C h + pivot_33 C h + pivot_13 C h + pivot_72 C h + pivot_57 C h + pivot_9 C h + pivot_66 C h

private theorem pivot_77 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 7 = C 0 0 + C 0 6 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    equation_3 C h + pivot_43 C h + pivot_4 C h + pivot_42 C h + pivot_7 C h + pivot_2 C h + pivot_5 C h + pivot_53 C h + pivot_73 C h + pivot_31 C h + pivot_51 C h + pivot_15 C h + pivot_21 C h + pivot_8 C h + pivot_33 C h + pivot_65 C h + pivot_13 C h + pivot_67 C h + pivot_88 C h + pivot_27 C h + pivot_37 C h + pivot_89 C h + pivot_58 C h + pivot_87 C h + pivot_18 C h + pivot_75 C h + pivot_17 C h + pivot_9 C h + pivot_69 C h + pivot_64 C h

private theorem entry_77 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 7 = C 0 0 + C 0 6 := by
  linear_combination (norm := ring_nf)
    pivot_77 C h

private theorem entry_68 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 8 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_68 C h

private theorem entry_64 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 4 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_64 C h

private theorem entry_69 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 9 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_69 C h

private theorem entry_66 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 6 = C 0 0 := by
  linear_combination (norm := ring_nf)
    pivot_66 C h + entry_64 C h

private theorem entry_9 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 9 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_9 C h + entry_69 C h

private theorem entry_17 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 7 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_17 C h

private theorem entry_19 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 9 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_19 C h

private theorem entry_74 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 4 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_74 C h

private theorem entry_39 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 9 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_39 C h

private theorem entry_75 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 5 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_75 C h

private theorem entry_57 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 7 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_57 C h

private theorem entry_72 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 2 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_72 C h

private theorem entry_54 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 4 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_54 C h

private theorem entry_63 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 3 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_63 C h + entry_68 C h

private theorem entry_18 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 8 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_18 C h + entry_75 C h

private theorem entry_87 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 7 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_87 C h + entry_72 C h

private theorem entry_58 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 8 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_58 C h + entry_57 C h

private theorem entry_89 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 9 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_89 C h + entry_72 C h

private theorem entry_37 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 7 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_37 C h + entry_58 C h

private theorem entry_27 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 7 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_27 C h + entry_18 C h

private theorem entry_28 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 8 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_28 C h + entry_17 C h

private theorem entry_88 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 8 = C 0 0 + C 0 6 := by
  linear_combination (norm := ring_nf)
    pivot_88 C h + entry_77 C h

private theorem entry_67 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 7 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_67 C h + entry_68 C h

private theorem entry_13 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 3 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_13 C h + entry_57 C h + entry_63 C h + entry_67 C h

private theorem entry_65 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 5 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_65 C h + entry_63 C h

private theorem entry_33 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 3 = C 0 0 + C 0 6 := by
  linear_combination (norm := ring_nf)
    pivot_33 C h + entry_65 C h + entry_68 C h + entry_88 C h

private theorem entry_32 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 2 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_32 C h + entry_57 C h + entry_72 C h + entry_87 C h

private theorem entry_8 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 8 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_8 C h + entry_63 C h + entry_89 C h

private theorem entry_55 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 5 = C 0 0 + C 0 6 := by
  linear_combination (norm := ring_nf)
    pivot_55 C h + entry_33 C h

private theorem entry_35 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    pivot_35 C h + entry_28 C h + entry_55 C h + entry_88 C h

private theorem entry_86 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 6 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_86 C h

private theorem entry_60 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 0 = C 0 6 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    pivot_60 C h + entry_66 C h

private theorem entry_25 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 5 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_25 C h + entry_13 C h

private theorem entry_81 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 1 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_81 C h + entry_72 C h

private theorem entry_71 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 1 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_71 C h + entry_25 C h + entry_35 C h + entry_81 C h

private theorem entry_82 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 2 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_82 C h + entry_71 C h

private theorem entry_61 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 1 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_61 C h + entry_35 C h + entry_65 C h + entry_71 C h

private theorem entry_21 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 1 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_21 C h + entry_32 C h + entry_37 C h + entry_87 C h

private theorem entry_23 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 3 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_23 C h + entry_32 C h + entry_61 C h + entry_65 C h

private theorem entry_38 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 8 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_38 C h + entry_28 C h + entry_72 C h + entry_82 C h

private theorem entry_62 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 6 2 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_62 C h + entry_38 C h + entry_68 C h + entry_72 C h

private theorem entry_15 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 5 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_15 C h + entry_23 C h

private theorem entry_51 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 1 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_51 C h + entry_32 C h

private theorem entry_31 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 1 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_31 C h + entry_15 C h + entry_51 C h + entry_75 C h

private theorem entry_52 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 2 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_52 C h + entry_18 C h + entry_62 C h + entry_68 C h

private theorem entry_73 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 3 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_73 C h + entry_21 C h + entry_31 C h + entry_75 C h

private theorem entry_22 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 2 = C 0 0 + C 0 6 := by
  linear_combination (norm := ring_nf)
    pivot_22 C h + entry_18 C h + entry_52 C h + entry_88 C h

private theorem entry_78 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    pivot_78 C h + entry_22 C h + entry_32 C h + entry_88 C h

private theorem entry_85 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 5 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_85 C h + entry_73 C h

private theorem entry_83 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 3 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_83 C h + entry_27 C h + entry_37 C h + entry_73 C h

private theorem entry_3 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 3 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_3 C h + entry_8 C h + entry_15 C h + entry_78 C h

private theorem entry_12 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    pivot_12 C h + entry_22 C h + entry_58 C h + entry_88 C h

private theorem entry_11 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 1 = C 0 0 + C 0 6 := by
  linear_combination (norm := ring_nf)
    pivot_11 C h + entry_21 C h + entry_55 C h + entry_85 C h

private theorem entry_53 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 3 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_53 C h + entry_17 C h + entry_27 C h + entry_83 C h

private theorem entry_80 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 0 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_80 C h

private theorem entry_99 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 9 = C 0 0 + C 0 6 := by
  linear_combination (norm := ring_nf)
    pivot_99 C h + entry_60 C h

private theorem entry_98 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 8 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_98 C h + entry_12 C h + entry_58 C h

private theorem entry_95 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := ZMod 2)]))
    pivot_95 C h + entry_11 C h + entry_55 C h

private theorem entry_93 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 3 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_93 C h + entry_17 C h + entry_53 C h

private theorem entry_5 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 5 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_5 C h + entry_3 C h

private theorem entry_1 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 1 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_1 C h + entry_5 C h + entry_95 C h

private theorem entry_2 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 2 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_2 C h + entry_1 C h

private theorem entry_7 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 7 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_7 C h + entry_3 C h + entry_93 C h

private theorem entry_48 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 8 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_48 C h + entry_5 C h + entry_8 C h

private theorem entry_47 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 7 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_47 C h + entry_1 C h + entry_7 C h

private theorem entry_42 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 2 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_42 C h + entry_2 C h + entry_3 C h

private theorem entry_84 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 8 4 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_84 C h

private theorem entry_4 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 0 4 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_4 C h + entry_64 C h

private theorem entry_44 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 4 = C 0 0 + C 0 6 := by
  linear_combination (norm := ring_nf)
    pivot_44 C h + entry_99 C h

private theorem entry_36 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 6 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_36 C h + entry_86 C h

private theorem entry_30 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 0 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_30 C h + entry_80 C h

private theorem entry_76 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 6 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_76 C h + entry_36 C h

private theorem entry_34 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 3 4 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_34 C h + entry_74 C h

private theorem entry_70 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 0 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_70 C h + entry_30 C h

private theorem entry_24 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 4 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_24 C h + entry_84 C h

private theorem entry_14 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 4 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_14 C h + entry_54 C h

private theorem entry_59 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 9 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_59 C h + entry_89 C h

private theorem entry_56 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 6 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_56 C h + entry_86 C h

private theorem entry_50 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 5 0 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_50 C h + entry_80 C h

private theorem entry_29 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 9 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_29 C h + entry_39 C h

private theorem entry_26 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 6 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_26 C h + entry_36 C h

private theorem entry_20 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 2 0 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_20 C h + entry_30 C h

private theorem entry_79 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 7 9 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_79 C h + entry_19 C h

private theorem entry_16 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 6 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_16 C h + entry_76 C h

private theorem entry_10 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 1 0 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_10 C h + entry_70 C h

private theorem entry_97 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 7 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_97 C h + entry_93 C h

private theorem entry_92 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 2 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_92 C h + entry_98 C h

private theorem entry_91 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 1 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_91 C h + entry_95 C h

private theorem entry_45 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 5 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_45 C h + entry_48 C h

private theorem entry_43 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 3 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_43 C h + entry_42 C h

private theorem entry_41 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 1 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_41 C h + entry_47 C h

private theorem entry_96 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 6 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_96 C h

private theorem entry_94 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 4 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_94 C h

private theorem entry_90 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 9 0 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_90 C h

private theorem entry_49 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 9 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_49 C h

private theorem entry_46 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 6 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_46 C h

private theorem entry_40 (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C 4 0 = 0 := by
  linear_combination (norm := ring_nf)
    pivot_40 C h


def swapMatrix : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  fun i j => if i = Equiv.swap (0 : Fin 10) 6 j then 1 else 0

theorem swapMatrix_check : permutationMatrix (Equiv.swap (0 : Fin 12) 6) = swapMatrix := by
  ext i j
  rw [permutationMatrix_formula]
  have h : ∀ (i j : Fin 10),
      (((if Fin.castAdd 2 i = Equiv.swap (0 : Fin 12) 6 (Fin.castAdd 2 j) then 1 else 0) +
        (if Fin.castAdd 2 i = Equiv.swap (0 : Fin 12) 6 11 then 1 else 0)) +
      ((if (10 : Fin 12) = Equiv.swap (0 : Fin 12) 6 (Fin.castAdd 2 j) then 1 else 0) +
        (if (10 : Fin 12) = Equiv.swap (0 : Fin 12) 6 11 then 1 else 0)) : ZMod 2) = swapMatrix i j := by
    exact @of_decide_eq_true _
      (@Nat.decidableForallFin 10 _ fun i => @Nat.decidableForallFin 10 _ fun j =>
        ZMod.decidableEq 2 _ _) (by decide +kernel)
  exact h i j

/-- The common endomorphism centralizer is contained in the span of the identity
and the swap of coordinates zero and six. -/
theorem centralizer_form (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (h : ∀ k, Commute C (wordMatrix k)) :
    C = C 0 0 • (1 : Matrix (Fin 10) (Fin 10) (ZMod 2)) + C 0 6 • swapMatrix := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simp [swapMatrix]
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_1 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_2 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_3 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_4 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_5 C h
  · simp [swapMatrix]
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_7 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_8 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_9 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_10 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_11 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_12 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_13 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_14 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_15 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_16 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_17 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_18 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_19 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_20 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_21 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_22 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_23 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_24 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_25 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_26 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_27 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_28 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_29 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_30 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_31 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_32 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_33 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_34 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_35 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_36 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_37 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_38 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_39 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_40 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_41 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_42 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_43 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_44 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_45 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_46 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_47 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_48 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_49 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_50 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_51 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_52 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_53 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_54 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_55 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_56 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_57 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_58 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_59 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_60 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_61 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_62 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_63 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_64 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_65 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_66 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_67 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_68 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_69 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_70 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_71 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_72 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_73 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_74 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_75 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_76 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_77 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_78 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_79 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_80 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_81 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_82 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_83 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_84 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_85 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_86 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_87 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_88 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_89 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_90 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_91 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_92 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_93 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_94 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_95 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_96 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_97 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_98 C h
  · simpa [Matrix.one_apply, swapMatrix, Equiv.swap_apply_def] using entry_99 C h

/-- Only two of the four centralizing matrices are invertible. -/
theorem centralizer_units (C : Matrix (Fin 10) (Fin 10) (ZMod 2))
    (hu : IsUnit C) (h : ∀ k, Commute C (wordMatrix k)) : C = 1 ∨ C = swapMatrix := by
  have hf := centralizer_form C h
  have binary (x : ZMod 2) : x = 0 ∨ x = 1 := by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases binary (C 0 0) with hx | hx <;> rcases binary (C 0 6) with hy | hy
  · have hz : C = 0 := by simpa [hx, hy] using hf
    exact False.elim (hu.ne_zero hz)
  · right
    simpa [hx, hy] using hf
  · left
    simpa [hx, hy] using hf
  · have hb : C = 1 + swapMatrix := by simpa [hx, hy] using hf
    rw [hb] at hu
    have hz : (1 + swapMatrix).mulVec (Pi.single (1 : Fin 10) (1 : ZMod 2)) = 0 := by
      decide +kernel
    have he := Matrix.mulVec_injective_of_isUnit hu (hz.trans (Matrix.mulVec_zero _).symm)
    have h10 : (1 : ZMod 2) = 0 := congrFun he 1
    exact False.elim (one_ne_zero h10)

end Representation.MathieuSmall.M12Recognition.PointExtension
