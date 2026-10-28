module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseFourExclusion.AutomizerData
public import Mathlib.Tactic.FinCases

/-!
# Binary columns for the Case IV automizer

The ordered basis is z₁,z₃,a,d. Little-endian indices identify its elementary
abelian group with sixteen binary vectors. We prove that four columns determine
an actual automorphism, that column multiplication interprets group words, and
that the three literal source generators have exactly the eight displayed
products. Their orbits reduce a moved first vector to 2, 4, 6 or 8.

These lemmas support the finite stabilizer exclusion in `FiniteRigidity`.
The coordinate proof pattern follows the independent Case II `FAction` proof;
all local matrices and finite identities here are checked for Case IV.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 1, printed pp.2–3,
DOI 10.1016/0021-8693(68)90002-1.
-/

namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseFour.FiniteRigidity

public abbrev Mat := Fin 4 → Fin 16
@[expose] public def basisIndex : Fin 4 → Fin 16 := ![1, 2, 4, 8]
@[expose] public def word (i : Fin 16) : BinaryFour := Multiplicative.ofAdd
  (fun j => if i.val.testBit j.val then 1 else 0)

public theorem word_injective : Function.Injective word := by decide +kernel
public theorem word_surjective : Function.Surjective word := by decide +kernel
public theorem word_zero : word 0 = 1 := by decide +kernel
public theorem word_one : word 1 = automizerPoint := by decide +kernel
public theorem word_xor : ∀ i j : Fin 16, word (i ^^^ j) = word i * word j := by decide +kernel

@[expose] public def act (m : Mat) (i : Fin 16) : Fin 16 :=
  (if i.val.testBit 0 then m 0 else 0) ^^^
  (if i.val.testBit 1 then m 1 else 0) ^^^
  (if i.val.testBit 2 then m 2 else 0) ^^^
  (if i.val.testBit 3 then m 3 else 0)
@[expose] public def mmul (m n : Mat) : Mat := fun i => act m (n i)

public theorem word_act (m : Mat) (i : Fin 16) :
    word (act m i) =
    (if i.val.testBit 0 then word (m 0) else 1) *
    (if i.val.testBit 1 then word (m 1) else 1) *
    (if i.val.testBit 2 then word (m 2) else 1) *
    (if i.val.testBit 3 then word (m 3) else 1) := by
  cases h0 : i.val.testBit 0 <;> cases h1 : i.val.testBit 1 <;>
    cases h2 : i.val.testBit 2 <;> cases h3 : i.val.testBit 3 <;>
    simp only [act, h0, h1, h2, h3, Bool.false_eq_true, if_false, if_true, word_xor, word_zero]

public theorem word_basis : ∀ i : Fin 16,
    word i =
    (if i.val.testBit 0 then word 1 else 1) *
    (if i.val.testBit 1 then word 2 else 1) *
    (if i.val.testBit 2 then word 4 else 1) *
    (if i.val.testBit 3 then word 8 else 1) := by decide +kernel

public theorem aut_word (f : MulAut BinaryFour) (m : Mat)
    (hm : ∀ j, f (word (basisIndex j)) = word (m j)) (i : Fin 16) :
    f (word i) = word (act m i) := by
  have h0 := hm 0
  have h1 := hm 1
  have h2 := hm 2
  have h3 := hm 3
  change f (word 1) = word (m 0) at h0
  change f (word 2) = word (m 1) at h1
  change f (word 4) = word (m 2) at h2
  change f (word 8) = word (m 3) at h3
  rw [word_act, word_basis i]
  cases b0 : i.val.testBit 0 <;> cases b1 : i.val.testBit 1 <;>
    cases b2 : i.val.testBit 2 <;> cases b3 : i.val.testBit 3 <;>
    simp only [Bool.false_eq_true, if_false, if_true,
      map_mul, map_one, h0, h1, h2, h3]

@[expose] public noncomputable def wordEquiv : Fin 16 ≃ BinaryFour :=
  Equiv.ofBijective word ⟨word_injective, word_surjective⟩
@[expose] public noncomputable def matrix (f : MulAut BinaryFour) : Mat :=
  fun i => wordEquiv.symm (f (word (basisIndex i)))
public theorem matrix_spec (f : MulAut BinaryFour) (i : Fin 4) :
    f (word (basisIndex i)) = word (matrix f i) :=
  (wordEquiv.apply_symm_apply _).symm
public theorem matrix_action (f : MulAut BinaryFour) (i : Fin 16) :
    f (word i) = word (act (matrix f) i) := aut_word f _ (matrix_spec f) i

public theorem matrix_injective : Function.Injective matrix := by
  intro f g h
  apply MulEquiv.ext
  intro x
  obtain ⟨i, rfl⟩ := word_surjective x
  rw [matrix_action, matrix_action, h]

public theorem matrix_eq_iff (f : MulAut BinaryFour) (m : Mat) :
    matrix f = m ↔ ∀ i, f (word (basisIndex i)) = word (m i) := by
  constructor
  · intro h i
    rw [matrix_spec, h]
  · intro h
    funext i
    apply word_injective
    exact (matrix_spec f i).symm.trans (h i)

public theorem matrix_mul (f g : MulAut BinaryFour) :
    matrix (f * g) = mmul (matrix f) (matrix g) := by
  apply (matrix_eq_iff _ _).mpr
  intro i
  change f (g (word (basisIndex i))) = _
  rw [matrix_spec, matrix_action]
  rfl

public theorem matrix_one : matrix 1 = basisIndex := by
  apply (matrix_eq_iff _ _).mpr
  intro i
  rfl

public theorem matrix_nonsingular (f : MulAut BinaryFour) (i : Fin 16)
    (hi : act (matrix f) i = 0) : i = 0 := by
  apply word_injective
  apply f.injective
  rw [matrix_action, hi, word_zero, map_one]

@[expose] public def localMat : Fin 3 → Mat :=
  ![![1, 2, 4, 9], ![1, 2, 5, 10], ![1, 3, 4, 12]]
@[expose] public def localTable : Fin 8 → Mat :=
  ![![1, 2, 4, 8], ![1, 2, 4, 9], ![1, 2, 5, 10], ![1, 2, 5, 11],
    ![1, 3, 4, 12], ![1, 3, 4, 13], ![1, 3, 5, 14], ![1, 3, 5, 15]]

public theorem matrix_generator (j : Fin 3) : matrix (automizerGenerator j) = localMat j := by
  apply (matrix_eq_iff _ _).mpr
  have h : ∀ j : Fin 3, ∀ i : Fin 4,
    automizerGenerator j (word (basisIndex i)) = word (localMat j i) := by decide +kernel
  exact h j

public theorem generator_mem (j : Fin 3) : automizerGenerator j ∈ localAutomizer :=
  Subgroup.subset_closure ⟨j, rfl⟩

public theorem matrix_of_mem_local (f : MulAut BinaryFour) (hf : f ∈ localAutomizer) :
    ∃ j : Fin 8, matrix f = localTable j := by
  induction hf using Subgroup.closure_induction with
  | mem f hf =>
    obtain ⟨j, rfl⟩ := hf
    rw [matrix_generator]
    have h : ∀ j : Fin 3, ∃ k : Fin 8, localMat j = localTable k := by decide +kernel
    exact h j
  | one => exact ⟨0, matrix_one⟩
  | mul f g _ _ hf hg =>
    obtain ⟨j, hj⟩ := hf
    obtain ⟨k, hk⟩ := hg
    rw [matrix_mul, hj, hk]
    have h : ∀ j k : Fin 8, ∃ l : Fin 8,
        mmul (localTable j) (localTable k) = localTable l := by decide +kernel
    exact h j k
  | inv f _ hf =>
    obtain ⟨j, hj⟩ := hf
    have h : ∀ j : Fin 8, mmul (localTable j) (localTable j) = basisIndex := by decide +kernel
    have hs : f * f = 1 := matrix_injective (by rw [matrix_mul, hj, h, matrix_one])
    rw [inv_eq_of_mul_eq_one_right hs]
    exact ⟨j, hj⟩

@[expose] public def generators (m : Mat) : Fin 4 → Mat := ![localMat 0, localMat 1, localMat 2, m]
@[expose] public def evalMat (m : Mat) : List (Fin 4) → Mat
  | [] => basisIndex
  | i :: w => mmul (generators m i) (evalMat m w)
@[expose] public def autGenerators (f : MulAut BinaryFour) : Fin 4 → MulAut BinaryFour :=
  ![automizerGenerator 0, automizerGenerator 1, automizerGenerator 2, f]
@[expose] public def evalAut (f : MulAut BinaryFour) : List (Fin 4) → MulAut BinaryFour
  | [] => 1
  | i :: w => autGenerators f i * evalAut f w

public theorem matrix_autGenerators (f : MulAut BinaryFour) (i : Fin 4) :
    matrix (autGenerators f i) = generators (matrix f) i := by
  fin_cases i
  · exact matrix_generator 0
  · exact matrix_generator 1
  · exact matrix_generator 2
  · rfl

public theorem matrix_evalAut (f : MulAut BinaryFour) (w : List (Fin 4)) :
    matrix (evalAut f w) = evalMat (matrix f) w := by
  induction w with
  | nil => exact matrix_one
  | cons i w ih =>
    change matrix (autGenerators f i * evalAut f w) = _
    rw [matrix_mul, matrix_autGenerators, ih]
    rfl

public theorem evalAut_mem (X : Subgroup (MulAut BinaryFour)) (hlocal : localAutomizer ≤ X)
    (f : MulAut BinaryFour) (hf : f ∈ X) (w : List (Fin 4)) : evalAut f w ∈ X := by
  have hg : ∀ i, autGenerators f i ∈ X := by
    intro i
    fin_cases i
    · exact hlocal (generator_mem 0)
    · exact hlocal (generator_mem 1)
    · exact hlocal (generator_mem 2)
    · exact hf
  induction w with
  | nil => exact X.one_mem
  | cons i w ih => exact X.mul_mem (hg i) ih

@[expose] public def localWords : Fin 8 → List (Fin 4) :=
  ![[], [0], [1], [0, 1], [2], [0, 2], [0, 1, 2], [1, 2]]
@[expose] public def localAut (j : Fin 8) : MulAut BinaryFour := evalAut 1 (localWords j)

public theorem localAut_mem (j : Fin 8) : localAut j ∈ localAutomizer :=
  evalAut_mem localAutomizer le_rfl 1 localAutomizer.one_mem _

public theorem matrix_localAut (j : Fin 8) : matrix (localAut j) = localTable j := by
  change matrix (evalAut 1 (localWords j)) = _
  rw [matrix_evalAut, matrix_one]
  have h : ∀ j : Fin 8, evalMat basisIndex (localWords j) = localTable j := by decide +kernel
  exact h j

@[expose] public def orbitRep : Fin 4 → Fin 16 := ![2, 4, 6, 8]

public theorem orbit_reduction : ∀ i : Fin 16, i ≠ 0 → i ≠ 1 →
    ∃ j : Fin 8, ∃ k : Fin 4, act (localTable j) i = orbitRep k := by decide +kernel

public theorem matrix_first_ne_zero (f : MulAut BinaryFour) : matrix f 0 ≠ 0 := by
  intro h
  have h' : f (word 1) = f (word 0) := by
    calc
      f (word 1) = word (matrix f 0) := matrix_spec f 0
      _ = word 0 := congrArg word h
      _ = f (word 0) := by rw [word_zero, map_one]
  have bad := word_injective (f.injective h')
  exact (by decide : (1 : Fin 16) ≠ 0) bad

public theorem fixes_point_iff (f : MulAut BinaryFour) :
    f automizerPoint = automizerPoint ↔ matrix f 0 = 1 := by
  have h : f automizerPoint = word (matrix f 0) := by
    simpa only [basisIndex, Matrix.cons_val_zero, word_one] using matrix_spec f 0
  rw [h, ← word_one]
  exact word_injective.eq_iff

/-- Multiplication by a literal local actor reduces every moved first vector
    to one of the four nontrivial local orbits. -/
public theorem normalize_first (f : MulAut BinaryFour) (hf : f automizerPoint ≠ automizerPoint) :
    ∃ j : Fin 8, ∃ k : Fin 4, matrix (localAut j * f) 0 = orbitRep k := by
  obtain ⟨j, k, h⟩ := orbit_reduction (matrix f 0) (matrix_first_ne_zero f)
    (fun h => hf ((fixes_point_iff f).mpr h))
  refine ⟨j, k, ?_⟩
  rw [matrix_mul, matrix_localAut]
  exact h

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseFour.FiniteRigidity
