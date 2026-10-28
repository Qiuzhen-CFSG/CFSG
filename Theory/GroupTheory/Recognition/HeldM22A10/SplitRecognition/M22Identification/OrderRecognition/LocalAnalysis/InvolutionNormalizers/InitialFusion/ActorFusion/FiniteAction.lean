module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.InitialFusion.ActorFusion.Coordinates
public import Mathlib.Data.Fin.Init

/-!
# A finite action proof of Janko's actor-fusion step

The group F has basis z₁, z₃, a, d. Encode its elements by four binary
bits, with multiplication given by xor. Conjugation by z₂z₃, z₄ and b gives
three explicit binary matrices; every local Sylow actor is one of eight
listed matrices.

For an automorphism taking z₁ to a, the other three basis images have
4096 possible values. A kernel-checked table selects one of 34 words in
that automorphism and the three local actors. The word either takes z₁
to d, or fixes z₁ and lies outside the eight local actors. The latter
contradicts the exact stabilizer hypothesis. This replaces the source's
small-index exclusions with a direct calculation in the actual Aut(F).

The selection table contains only witnesses: every entry is checked in
Lean, as are the coordinate multiplication and all local action matrices.
The checks are partitioned by the second column to limit kernel memory.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, paragraph preceding Lemma 3, printed p.5.
Source indices are one-based, while the existing CaseII.z indices are zero-based.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII.ActorFusion
open LocalModelDichotomy

local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm
local instance : DecidablePred (· ∈ modelF) := fun x =>
  decidable_of_iff (x * d = d * x) mem_centralizer_singleton_iff.symm
local instance : DecidablePred (· ∈ modelT) := fun x =>
  decidable_of_iff (x.right * a.right = a.right * x.right) mem_centralizer_singleton_iff.symm

abbrev z2F : modelF := ⟨z 2, modelF_generators.2.1⟩
def word (i : Fin 16) : modelF :=
  (if i.val.testBit 0 then zF else 1) *
  (if i.val.testBit 1 then z2F else 1) *
  (if i.val.testBit 2 then aF else 1) *
  (if i.val.testBit 3 then dF else 1)

theorem word_zero : word 0 = 1 := by decide +kernel
theorem word_injective : Function.Injective word := by decide +kernel
theorem word_surjective : Function.Surjective word := by decide +kernel
theorem word_xor : ∀ i j : Fin 16, word (i ^^^ j) = word i * word j := by decide +kernel

def basisIndex : Fin 4 → Fin 16 := ![1,2,4,8]
theorem word_basis : ∀ i : Fin 4, word (basisIndex i) = ![zF,z2F,aF,dF] i := by decide +kernel

abbrev Mat := Fin 4 → Fin 16
def act (m : Mat) (i : Fin 16) : Fin 16 :=
  (if i.val.testBit 0 then m 0 else 0) ^^^
  (if i.val.testBit 1 then m 1 else 0) ^^^
  (if i.val.testBit 2 then m 2 else 0) ^^^
  (if i.val.testBit 3 then m 3 else 0)
def mmul (m n : Mat) : Mat := ![act m (n 0),act m (n 1),act m (n 2),act m (n 3)]
def ident : Mat := basisIndex

theorem word_act (m : Mat) (i : Fin 16) :
    word (act m i) =
    (if i.val.testBit 0 then word (m 0) else 1) *
    (if i.val.testBit 1 then word (m 1) else 1) *
    (if i.val.testBit 2 then word (m 2) else 1) *
    (if i.val.testBit 3 then word (m 3) else 1) := by
  cases h0 : i.val.testBit 0 <;> cases h1 : i.val.testBit 1 <;>
    cases h2 : i.val.testBit 2 <;> cases h3 : i.val.testBit 3 <;>
    simp only [act, h0, h1, h2, h3, Bool.false_eq_true, if_false, if_true, word_xor, word_zero]

theorem aut_word (f : MulAut modelF) (m : Mat)
    (hm : ∀ j, f (word (basisIndex j)) = word (m j)) (i : Fin 16) :
    f (word i) = word (act m i) := by
  have h0 := hm 0
  have h1 := hm 1
  have h2 := hm 2
  have h3 := hm 3
  rw [word_basis] at h0 h1 h2 h3
  change f zF = word (m 0) at h0
  change f z2F = word (m 1) at h1
  change f aF = word (m 2) at h2
  change f dF = word (m 3) at h3
  rw [word_act]
  cases b0 : i.val.testBit 0 <;> cases b1 : i.val.testBit 1 <;>
    cases b2 : i.val.testBit 2 <;> cases b3 : i.val.testBit 3 <;>
    simp only [word, b0, b1, b2, b3, Bool.false_eq_true, if_false, if_true,
      map_mul, map_one, h0, h1, h2, h3]

def localMat : Fin 3 → Mat := ![![1,2,7,9], ![1,2,5,10], ![1,3,4,12]]
def bMat : Fin 8 → Mat :=
  ![![1,2,4,8], ![1,2,5,10], ![1,2,6,11], ![1,2,7,9],
    ![1,3,4,12], ![1,3,5,15], ![1,3,6,13], ![1,3,7,14]]
def localGen (i : Fin 3) : modelT :=
  ⟨![z 1 * z 2, z 3, b] i, by
    have h : ∀ i : Fin 3, ![z 1 * z 2, z 3, b] i ∈ modelT := by decide +kernel
    exact h i⟩
theorem localGen_mat : ∀ j : Fin 3, ∀ i : Fin 4,
    localAction (localGen j) (word (basisIndex i)) = word (localMat j i) := by decide +kernel

theorem localAction_mat : ∀ x : modelT, ∃ j : Fin 8,
    ∀ i : Fin 4, localAction x (word (basisIndex i)) = word (bMat j i) := by decide +kernel

def generators (m : Mat) : Fin 4 → Mat := ![localMat 0,localMat 1,localMat 2,m]
def evalMat (m : Mat) : List (Fin 4) → Mat
  | [] => ident
  | i :: w => mmul (evalMat m w) (generators m i)

def witnesses : Fin 34 → List (Fin 4) :=
  ![[3,3], [3,0,3], [3,1,3], [3,2,3], [3,3,0], [3,3,1], [3,3,3],
    [3,0,1,3], [3,0,2,3], [3,0,3,0], [3,0,3,1], [3,0,3,3],
    [3,1,2,3], [3,1,3,0], [3,1,3,1], [3,1,3,3], [3,2,0,3], [3,2,3,3],
    [3,3,0,1], [3,3,0,3], [3,3,1,2], [3,3,1,3], [3,3,2,3],
    [3,3,3,0], [3,3,3,1], [3,3,3,3], [3,0,1,3,0], [3,0,1,3,1],
    [3,0,1,3,3], [3,0,3,0,1], [3,0,3,0,3], [3,0,3,1,2], [3,0,3,1,3], [3,0,3,3,3]]

def choiceRow0 : Fin 16 → Fin 16 → Fin 34 :=
  ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def choiceRow1 : Fin 16 → Fin 16 → Fin 34 :=
  ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 17, 6, 6, 19, 6, 17, 19, 6],
    ![0, 0, 0, 0, 0, 0, 0, 0, 22, 22, 22, 33, 22, 22, 33, 22],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 15, 15, 15, 15, 15, 15, 15, 15],
    ![0, 0, 0, 0, 0, 0, 0, 0, 11, 11, 11, 11, 11, 11, 11, 11],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4],
    ![0, 0, 5, 5, 0, 0, 5, 5, 5, 5, 0, 0, 5, 5, 0, 0],
    ![0, 0, 11, 18, 0, 0, 15, 18, 18, 18, 0, 0, 18, 6, 0, 0],
    ![0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2],
    ![0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1],
    ![0, 0, 14, 14, 0, 0, 14, 6, 14, 14, 0, 0, 14, 11, 0, 0],
    ![0, 0, 6, 10, 0, 0, 10, 10, 10, 10, 0, 0, 10, 10, 0, 0]]

def choiceRow2 : Fin 16 → Fin 16 → Fin 34 :=
  ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0, 3, 0, 3],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 7, 8, 7, 8, 8, 7, 8, 7],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 12, 2, 6, 2, 2, 12, 2, 6],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 6, 1, 16, 6, 1, 16, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 4, 0, 4, 0, 4, 0, 4, 4, 0, 4, 0, 4, 0, 4, 0],
    ![0, 5, 0, 5, 0, 5, 0, 5, 0, 5, 0, 5, 0, 5, 0, 5],
    ![0, 18, 0, 18, 0, 15, 0, 11, 18, 0, 18, 0, 15, 0, 6, 0],
    ![0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2],
    ![0, 6, 0, 13, 0, 13, 0, 11, 13, 0, 13, 0, 13, 0, 11, 0],
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![0, 6, 0, 9, 0, 9, 0, 9, 9, 0, 9, 0, 9, 0, 9, 0]]

def choiceRow3 : Fin 16 → Fin 16 → Fin 34 :=
  ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 7, 7, 7, 7, 7, 7, 7, 7],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 4, 4, 0, 0, 4, 4, 0, 4, 0, 0, 4, 4, 0, 0, 4],
    ![0, 5, 5, 0, 0, 5, 5, 0, 5, 0, 0, 5, 5, 0, 0, 5],
    ![0, 7, 7, 0, 0, 7, 6, 0, 0, 7, 7, 0, 0, 7, 7, 0],
    ![0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0],
    ![0, 6, 10, 0, 0, 10, 10, 0, 6, 0, 0, 10, 10, 0, 0, 10],
    ![0, 9, 9, 0, 0, 6, 9, 0, 9, 0, 0, 9, 6, 0, 0, 9],
    ![0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0]]

def choiceRow4 : Fin 16 → Fin 16 → Fin 34 :=
  ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def choiceRow5 : Fin 16 → Fin 16 → Fin 34 :=
  ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 11, 32, 11, 11, 32, 11, 11, 11],
    ![0, 0, 0, 0, 0, 0, 0, 0, 21, 6, 17, 6, 6, 21, 6, 17],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 28, 28, 28, 28, 28, 28, 28, 28],
    ![0, 0, 0, 0, 0, 0, 0, 0, 15, 15, 15, 15, 15, 15, 15, 15],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1],
    ![0, 0, 5, 5, 0, 0, 5, 5, 5, 5, 0, 0, 5, 5, 0, 0],
    ![0, 0, 10, 10, 0, 0, 10, 10, 10, 6, 0, 0, 10, 10, 0, 0],
    ![0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2],
    ![0, 0, 7, 7, 0, 0, 7, 7, 0, 0, 7, 7, 0, 0, 7, 7],
    ![0, 0, 14, 6, 0, 0, 14, 11, 14, 14, 0, 0, 14, 14, 0, 0],
    ![0, 0, 11, 19, 0, 0, 6, 20, 20, 15, 0, 0, 20, 20, 0, 0]]

def choiceRow6 : Fin 16 → Fin 16 → Fin 34 :=
  ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 7, 7, 7, 7, 7, 7, 7, 7],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 4, 0, 4, 0, 4, 0, 4, 4, 0, 4, 0, 4, 0, 4, 0],
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![0, 9, 0, 6, 0, 9, 0, 9, 9, 0, 6, 0, 9, 0, 9, 0],
    ![0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2],
    ![0, 6, 0, 13, 0, 13, 0, 11, 6, 0, 13, 0, 13, 0, 11, 0],
    ![0, 7, 0, 7, 0, 7, 0, 7, 0, 6, 0, 7, 0, 7, 0, 7],
    ![0, 20, 0, 11, 0, 6, 0, 20, 20, 0, 11, 0, 6, 0, 20, 0]]

def choiceRow7 : Fin 16 → Fin 16 → Fin 34 :=
  ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 3, 3, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 16, 16, 1, 16, 1, 1, 16],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, 12, 6, 2, 12, 2, 2, 6],
    ![0, 0, 0, 0, 0, 0, 0, 0, 8, 6, 7, 6, 6, 8, 6, 7],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 4, 4, 0, 0, 4, 4, 0, 4, 0, 0, 4, 4, 0, 0, 4],
    ![0, 5, 5, 0, 0, 5, 5, 0, 5, 0, 0, 5, 5, 0, 0, 5],
    ![0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0],
    ![0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0],
    ![0, 6, 11, 0, 0, 13, 13, 0, 13, 0, 0, 11, 13, 0, 0, 13],
    ![0, 6, 11, 0, 0, 14, 14, 0, 14, 0, 0, 11, 14, 0, 0, 14],
    ![0, 7, 7, 0, 0, 7, 7, 0, 0, 7, 7, 0, 0, 7, 7, 0]]

def choiceRow8 : Fin 16 → Fin 16 → Fin 34 :=
  ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 26, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 6, 0, 6, 0, 6, 0, 6, 0, 6, 0, 6, 0, 6, 0, 6],
    ![0, 22, 22, 0, 0, 22, 22, 0, 0, 22, 22, 0, 0, 22, 11, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 9, 6, 0, 0, 2, 2],
    ![0, 10, 0, 10, 0, 10, 0, 10, 0, 10, 0, 10, 0, 10, 0, 10],
    ![0, 29, 29, 0, 0, 29, 29, 0, 0, 29, 28, 0, 0, 11, 29, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4, 0, 0, 4, 4],
    ![0, 5, 0, 5, 0, 5, 0, 5, 0, 5, 0, 5, 0, 5, 0, 5],
    ![0, 18, 18, 0, 0, 18, 15, 0, 0, 18, 18, 0, 0, 17, 18, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 13, 13, 0, 0, 1, 1, 0, 0, 1, 1],
    ![0, 11, 0, 11, 0, 11, 0, 11, 0, 11, 0, 11, 0, 11, 0, 11],
    ![0, 20, 6, 0, 0, 20, 20, 0, 0, 20, 19, 0, 0, 15, 20, 0]]

def choiceRow9 : Fin 16 → Fin 16 → Fin 34 :=
  ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 7, 7, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 23, 0, 23, 0, 23, 0, 11, 23, 0, 23, 0, 23, 0, 11, 0],
    ![0, 27, 11, 0, 0, 27, 27, 0, 27, 0, 0, 11, 27, 0, 0, 25],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1],
    ![0, 29, 0, 25, 0, 11, 0, 29, 29, 0, 28, 0, 11, 0, 29, 0],
    ![0, 10, 10, 0, 0, 10, 10, 0, 10, 0, 0, 10, 10, 0, 0, 10],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 5, 5, 0, 0, 5, 5, 0, 5, 0, 0, 5, 5, 0, 0, 5],
    ![0, 18, 0, 18, 0, 6, 0, 15, 18, 0, 18, 0, 6, 0, 15, 0],
    ![0, 0, 2, 2, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 14, 14, 0, 0, 14, 6, 0, 14, 0, 0, 14, 14, 0, 0, 6],
    ![0, 20, 0, 17, 0, 15, 0, 20, 20, 0, 6, 0, 15, 0, 20, 0]]

def choiceRow10 : Fin 16 → Fin 16 → Fin 34 :=
  ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0],
    ![0, 7, 0, 7, 0, 7, 0, 7, 0, 7, 0, 7, 0, 7, 0, 7],
    ![0, 25, 26, 0, 0, 26, 11, 0, 26, 0, 0, 26, 26, 0, 0, 11],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 12, 2, 0, 0, 2, 2, 2, 2, 0, 0, 2, 2, 0, 0],
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![0, 9, 9, 0, 0, 9, 9, 0, 9, 0, 0, 9, 9, 0, 0, 9],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 4, 4, 0, 0, 4, 4, 0, 4, 0, 0, 4, 4, 0, 0, 4],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 7, 7, 0, 0, 6, 7, 7, 7, 0, 0, 7, 7, 0, 0],
    ![0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2],
    ![0, 6, 13, 0, 0, 13, 13, 0, 6, 0, 0, 13, 13, 0, 0, 13],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 16, 1, 0, 0]]

def choiceRow11 : Fin 16 → Fin 16 → Fin 34 :=
  ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0],
    ![0, 26, 0, 26, 0, 26, 0, 11, 26, 0, 26, 0, 26, 0, 11, 0],
    ![0, 7, 7, 0, 0, 7, 7, 0, 0, 7, 7, 0, 0, 7, 7, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 2, 0, 0, 10, 2, 2, 2, 0, 0, 2, 2, 0, 0],
    ![0, 9, 0, 9, 0, 9, 0, 9, 9, 0, 9, 0, 9, 0, 9, 0],
    ![0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 4, 0, 4, 0, 4, 0, 4, 4, 0, 4, 0, 4, 0, 4, 0],
    ![0, 0, 5, 5, 0, 0, 5, 5, 5, 5, 0, 0, 5, 5, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0],
    ![0, 6, 0, 13, 0, 13, 0, 13, 13, 0, 13, 0, 13, 0, 13, 0],
    ![0, 0, 1, 1, 0, 0, 1, 1, 1, 14, 0, 0, 1, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def choiceRow12 : Fin 16 → Fin 16 → Fin 34 :=
  ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 9, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 10, 0, 10, 0, 10, 0, 10, 0, 10, 0, 10, 0, 10, 0, 10],
    ![0, 6, 6, 0, 0, 6, 6, 0, 0, 6, 6, 0, 0, 6, 6, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 6, 26],
    ![0, 24, 0, 24, 0, 24, 0, 24, 0, 24, 0, 11, 0, 24, 0, 24],
    ![0, 15, 15, 0, 0, 15, 15, 0, 0, 15, 15, 0, 0, 15, 11, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 4, 4, 0, 0, 1, 1, 0, 0, 1, 1],
    ![0, 5, 0, 5, 0, 5, 0, 5, 0, 5, 0, 5, 0, 5, 0, 5],
    ![0, 11, 11, 0, 0, 11, 11, 0, 0, 6, 11, 0, 0, 11, 11, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 7, 7, 0, 0, 7, 7, 0, 0, 13, 13, 0, 0, 7, 7],
    ![0, 14, 0, 6, 0, 14, 0, 14, 0, 14, 0, 14, 0, 14, 0, 14],
    ![0, 20, 20, 0, 0, 20, 17, 0, 0, 15, 19, 0, 0, 20, 20, 0]]

def choiceRow13 : Fin 16 → Fin 16 → Fin 34 :=
  ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 11, 0, 28, 0, 29, 0, 29, 11, 0, 28, 0, 29, 0, 25, 0],
    ![0, 10, 10, 0, 0, 10, 10, 0, 10, 0, 0, 10, 10, 0, 0, 10],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 7, 6, 0, 0, 2, 2],
    ![0, 25, 0, 30, 0, 31, 0, 11, 28, 0, 30, 0, 31, 0, 11, 0],
    ![0, 27, 11, 0, 0, 27, 27, 0, 27, 0, 0, 11, 27, 0, 0, 27],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 5, 5, 0, 0, 5, 5, 0, 5, 0, 0, 5, 5, 0, 0, 5],
    ![0, 6, 0, 15, 0, 18, 0, 18, 17, 0, 15, 0, 18, 0, 18, 0],
    ![0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 14, 14, 0, 0, 14, 14, 0, 14, 0, 0, 6, 14, 0, 0, 14],
    ![0, 15, 0, 19, 0, 20, 0, 6, 15, 0, 19, 0, 20, 0, 6, 0]]

def choiceRow14 : Fin 16 → Fin 16 → Fin 34 :=
  ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0],
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![0, 9, 9, 0, 0, 9, 9, 0, 9, 0, 0, 9, 9, 0, 0, 9],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 6, 0, 0, 2, 2, 2, 2, 0, 0, 2, 2, 0, 0],
    ![0, 6, 0, 6, 0, 6, 0, 6, 0, 6, 0, 6, 0, 6, 0, 6],
    ![0, 26, 11, 0, 0, 26, 26, 0, 26, 0, 0, 11, 26, 0, 0, 26],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 4, 4, 0, 0, 4, 4, 0, 4, 0, 0, 4, 4, 0, 0, 4],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 1, 1, 1, 15, 0, 0, 1, 1, 0, 0],
    ![0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2],
    ![0, 6, 13, 0, 0, 13, 13, 0, 13, 0, 0, 13, 13, 0, 0, 13],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 7, 7, 0, 0, 7, 8, 7, 7, 0, 0, 7, 6, 0, 0]]

def choiceRow15 : Fin 16 → Fin 16 → Fin 34 :=
  ![
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0],
    ![0, 9, 0, 9, 0, 9, 0, 9, 9, 0, 9, 0, 9, 0, 9, 0],
    ![0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 2, 0, 0, 2, 6, 2, 2, 0, 0, 2, 2, 0, 0],
    ![0, 23, 0, 11, 0, 23, 0, 23, 23, 0, 11, 0, 23, 0, 23, 0],
    ![0, 7, 7, 0, 0, 7, 7, 0, 0, 7, 7, 0, 0, 7, 7, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 4, 0, 4, 0, 4, 0, 4, 4, 0, 4, 0, 4, 0, 4, 0],
    ![0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 5, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0],
    ![0, 6, 0, 13, 0, 13, 0, 13, 6, 0, 13, 0, 13, 0, 13, 0],
    ![0, 0, 7, 8, 0, 0, 7, 7, 7, 6, 0, 0, 7, 7, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def pick (r : Fin 3 → Fin 16) : Fin 34 :=
  ![choiceRow0, choiceRow1, choiceRow2, choiceRow3, choiceRow4, choiceRow5, choiceRow6, choiceRow7, choiceRow8, choiceRow9, choiceRow10, choiceRow11, choiceRow12, choiceRow13, choiceRow14, choiceRow15] (r 0) (r 1) (r 2)

def Verified (r : Fin 3 → Fin 16) : Prop :=
    let m : Mat := ![4,r 0,r 1,r 2]
    (∀ i : Fin 16, act m i = 0 → i = 0) →
    (evalMat m (witnesses (pick r))) 0 = 8 ∨
      ((evalMat m (witnesses (pick r))) 0 = 1 ∧
        ∀ b : Fin 8, evalMat m (witnesses (pick r)) ≠ bMat b)

instance (r : Fin 3 → Fin 16) : Decidable (Verified r) :=
  inferInstanceAs (Decidable (_ → _ ∨ _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verifyRow0 : ∀ y z : Fin 16, Verified ![0,y,z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verifyRow1 : ∀ y z : Fin 16, Verified ![1,y,z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verifyRow2 : ∀ y z : Fin 16, Verified ![2,y,z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verifyRow3 : ∀ y z : Fin 16, Verified ![3,y,z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verifyRow4 : ∀ y z : Fin 16, Verified ![4,y,z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verifyRow5 : ∀ y z : Fin 16, Verified ![5,y,z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verifyRow6 : ∀ y z : Fin 16, Verified ![6,y,z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verifyRow7 : ∀ y z : Fin 16, Verified ![7,y,z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verifyRow8 : ∀ y z : Fin 16, Verified ![8,y,z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verifyRow9 : ∀ y z : Fin 16, Verified ![9,y,z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verifyRow10 : ∀ y z : Fin 16, Verified ![10,y,z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verifyRow11 : ∀ y z : Fin 16, Verified ![11,y,z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verifyRow12 : ∀ y z : Fin 16, Verified ![12,y,z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verifyRow13 : ∀ y z : Fin 16, Verified ![13,y,z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verifyRow14 : ∀ y z : Fin 16, Verified ![14,y,z] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem verifyRow15 : ∀ y z : Fin 16, Verified ![15,y,z] := by decide +kernel

theorem verifyCols (x y z : Fin 16) : Verified ![x,y,z] := by
  fin_cases x
  · exact verifyRow0 y z
  · exact verifyRow1 y z
  · exact verifyRow2 y z
  · exact verifyRow3 y z
  · exact verifyRow4 y z
  · exact verifyRow5 y z
  · exact verifyRow6 y z
  · exact verifyRow7 y z
  · exact verifyRow8 y z
  · exact verifyRow9 y z
  · exact verifyRow10 y z
  · exact verifyRow11 y z
  · exact verifyRow12 y z
  · exact verifyRow13 y z
  · exact verifyRow14 y z
  · exact verifyRow15 y z

theorem verify (r : Fin 3 → Fin 16) : Verified r := by
  have hr : r = ![r 0,r 1,r 2] := by funext i; fin_cases i <;> rfl
  rw [hr]
  exact verifyCols (r 0) (r 1) (r 2)

theorem certificate (r : Fin 3 → Fin 16)
    (h : ∀ i : Fin 16, act ![4,r 0,r 1,r 2] i = 0 → i = 0) :
    ∃ j : Fin 34, (evalMat ![4,r 0,r 1,r 2] (witnesses j)) 0 = 8 ∨
      ((evalMat ![4,r 0,r 1,r 2] (witnesses j)) 0 = 1 ∧
        ∀ b : Fin 8, evalMat ![4,r 0,r 1,r 2] (witnesses j) ≠ bMat b) :=
  ⟨pick r, verify r h⟩

def autGenerators (f : MulAut modelF) : Fin 4 → MulAut modelF :=
  ![localAction (localGen 0),localAction (localGen 1),localAction (localGen 2),f]
def evalAut (f : MulAut modelF) : List (Fin 4) → MulAut modelF
  | [] => 1
  | i :: w => evalAut f w * autGenerators f i

theorem mmul_apply (m n : Mat) (i : Fin 4) : mmul m n i = act m (n i) := by
  fin_cases i <;> rfl

theorem generators_spec (f : MulAut modelF) (m : Mat)
    (hm : ∀ i, f (word (basisIndex i)) = word (m i)) :
    ∀ j i, autGenerators f j (word (basisIndex i)) = word (generators m j i) := by
  intro j i
  fin_cases j
  · exact localGen_mat 0 i
  · exact localGen_mat 1 i
  · exact localGen_mat 2 i
  · exact hm i

theorem eval_spec (f : MulAut modelF) (m : Mat)
    (hm : ∀ i, f (word (basisIndex i)) = word (m i)) (w : List (Fin 4)) :
    ∀ i, evalAut f w (word (basisIndex i)) = word (evalMat m w i) := by
  induction w with
  | nil => intro i; rfl
  | cons j w ih =>
    intro i
    change evalAut f w (autGenerators f j (word (basisIndex i))) =
      word (mmul (evalMat m w) (generators m j) i)
    rw [generators_spec f m hm, mmul_apply, aut_word (evalAut f w) (evalMat m w) ih]

theorem eval_mem (A : Subgroup (MulAut modelF)) (hA : localActor ≤ A)
    (f : MulAut modelF) (hf : f ∈ A) (w : List (Fin 4)) : evalAut f w ∈ A := by
  have hg : ∀ j, autGenerators f j ∈ A := by
    intro j
    fin_cases j
    · exact hA ⟨localGen 0, rfl⟩
    · exact hA ⟨localGen 1, rfl⟩
    · exact hA ⟨localGen 2, rfl⟩
    · exact hf
  induction w with
  | nil => exact A.one_mem
  | cons j w ih => exact A.mul_mem ih (hg j)

/-- If the stabilizer of z₁ is exactly the local Sylow action, fusion of
z₁ with a forces fusion with d in the same actual automorphism group. -/
public theorem finite_actor_fusion (A : Subgroup (MulAut modelF))
    (hA : localActor ≤ A)
    (hstab : ∀ f ∈ A, f zF = zF → f ∈ localActor)
    (ha : ∃ f ∈ A, f zF = aF) : ∃ f ∈ A, f zF = dF := by
  obtain ⟨f, hf, hfa⟩ := ha
  obtain ⟨r0, hr0⟩ := word_surjective (f z2F)
  obtain ⟨r1, hr1⟩ := word_surjective (f aF)
  obtain ⟨r2, hr2⟩ := word_surjective (f dF)
  let r : Fin 3 → Fin 16 := ![r0,r1,r2]
  let m : Mat := ![4,r 0,r 1,r 2]
  have hm : ∀ i, f (word (basisIndex i)) = word (m i) := by
    intro i
    fin_cases i
    all_goals rw [word_basis]
    · change f zF = word 4
      rw [show word 4 = aF by decide +kernel]
      exact hfa
    · exact hr0.symm
    · exact hr1.symm
    · exact hr2.symm
  have hinj : ∀ i : Fin 16, act m i = 0 → i = 0 := by
    intro i hi
    apply word_injective
    apply f.injective
    rw [aut_word f m hm, hi, word_zero, map_one]
  obtain ⟨j, hj⟩ := certificate r hinj
  let w := witnesses j
  let g := evalAut f w
  have hg : g ∈ A := eval_mem A hA f hf w
  have hz : word 1 = zF := by decide +kernel
  have hd : word 8 = dF := by decide +kernel
  have hg0 := eval_spec f m hm w 0
  change g (word 1) = word (evalMat m w 0) at hg0
  rcases hj with hj | ⟨hj, hout⟩
  · refine ⟨g, hg, ?_⟩
    change evalMat m w 0 = 8 at hj
    simpa only [hz, hj, hd] using hg0
  · have hgz : g zF = zF := by
      change evalMat m w 0 = 1 at hj
      simpa only [hz, hj] using hg0
    obtain ⟨x, hx⟩ := hstab g hg hgz
    obtain ⟨t, ht⟩ := localAction_mat x
    apply False.elim
    apply hout t
    funext i
    apply word_injective
    calc
      word (evalMat m w i) = g (word (basisIndex i)) := (eval_spec f m hm w i).symm
      _ = localAction x (word (basisIndex i)) := by rw [hx]
      _ = word (bMat t i) := ht i

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII.ActorFusion
