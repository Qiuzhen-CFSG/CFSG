module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.FAction.Coordinates

/-!
# Matrix coordinates for the finite F-automizer identification

The four columns record the images of z₁,z₃,a,d in the already proved word
coordinates on the actual elementary sixteen. Matrix evaluation and products
are related to actual multiplicative automorphisms, and the eight local
matrices are certified against conjugation by the coordinate normalizer.

This is coordinate infrastructure for the finite step in Janko's Lemma 2;
it does not assert any classification of linear groups.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, pp.4–5. The local matrix calculation also
appears in the independent actor-fusion proof in InitialFusion/ActorFusion.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII.FAction.Identification
open LocalModelDichotomy

local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm
local instance : DecidablePred (· ∈ modelF) := fun x =>
  decidable_of_iff (x * d = d * x) mem_centralizer_singleton_iff.symm
local instance : DecidablePred (· ∈ modelT) := fun x =>
  decidable_of_iff (x.right * a.right = a.right * x.right) mem_centralizer_singleton_iff.symm

public abbrev Mat := Fin 4 → Fin 16
@[expose] public def basisIndex : Fin 4 → Fin 16 := ![1, 2, 4, 8]
@[expose] public def act (m : Mat) (i : Fin 16) : Fin 16 :=
  (if i.val.testBit 0 then m 0 else 0) ^^^
  (if i.val.testBit 1 then m 1 else 0) ^^^
  (if i.val.testBit 2 then m 2 else 0) ^^^
  (if i.val.testBit 3 then m 3 else 0)
@[expose] public def mmul (m n : Mat) : Mat := fun i => act m (n i)

public theorem word_basis : ∀ i : Fin 4,
    word (basisIndex i) = ![pointZ, pointY, pointA, pointD] i := by decide +kernel

public theorem word_act (m : Mat) (i : Fin 16) :
    word (act m i) =
    (if i.val.testBit 0 then word (m 0) else 1) *
    (if i.val.testBit 1 then word (m 1) else 1) *
    (if i.val.testBit 2 then word (m 2) else 1) *
    (if i.val.testBit 3 then word (m 3) else 1) := by
  cases h0 : i.val.testBit 0 <;> cases h1 : i.val.testBit 1 <;>
    cases h2 : i.val.testBit 2 <;> cases h3 : i.val.testBit 3 <;>
    simp only [act, h0, h1, h2, h3, Bool.false_eq_true, if_false, if_true, word_xor, word_zero]

public theorem aut_word (f : MulAut modelF) (m : Mat)
    (hm : ∀ j, f (word (basisIndex j)) = word (m j)) (i : Fin 16) :
    f (word i) = word (act m i) := by
  have h0 := hm 0
  have h1 := hm 1
  have h2 := hm 2
  have h3 := hm 3
  rw [word_basis] at h0 h1 h2 h3
  change f pointZ = word (m 0) at h0
  change f pointY = word (m 1) at h1
  change f pointA = word (m 2) at h2
  change f pointD = word (m 3) at h3
  rw [word_act]
  cases b0 : i.val.testBit 0 <;> cases b1 : i.val.testBit 1 <;>
    cases b2 : i.val.testBit 2 <;> cases b3 : i.val.testBit 3 <;>
    simp only [word, b0, b1, b2, b3, Bool.false_eq_true, if_false, if_true,
      map_mul, map_one, h0, h1, h2, h3]

/-- The previously verified coordinates, packaged as a bijection. -/
@[expose] public noncomputable def wordEquiv : Fin 16 ≃ modelF :=
  Equiv.ofBijective word ⟨word_injective, word_surjective⟩

@[simp] public theorem wordEquiv_apply (i : Fin 16) : wordEquiv i = word i := rfl

/-- Columns of an actual automorphism, with no choice of a different carrier. -/
@[expose] public noncomputable def matrix (f : MulAut modelF) : Mat :=
  fun i => wordEquiv.symm (f (word (basisIndex i)))

public theorem matrix_spec (f : MulAut modelF) (i : Fin 4) :
    f (word (basisIndex i)) = word (matrix f i) :=
  (wordEquiv.apply_symm_apply _).symm

public theorem matrix_action (f : MulAut modelF) (i : Fin 16) :
    f (word i) = word (act (matrix f) i) := aut_word f _ (matrix_spec f) i

public theorem matrix_injective : Function.Injective matrix := by
  intro f g h
  apply MulEquiv.ext
  intro x
  obtain ⟨i, rfl⟩ := word_surjective x
  rw [matrix_action, matrix_action, h]

public theorem matrix_eq_iff (f : MulAut modelF) (m : Mat) :
    matrix f = m ↔ ∀ i, f (word (basisIndex i)) = word (m i) := by
  constructor
  · intro h i
    rw [matrix_spec, h]
  · intro h
    funext i
    apply word_injective
    exact (matrix_spec f i).symm.trans (h i)

public theorem matrix_mul (f g : MulAut modelF) :
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

public theorem matrix_nonsingular (f : MulAut modelF) (i : Fin 16)
    (hi : act (matrix f) i = 0) : i = 0 := by
  apply word_injective
  apply f.injective
  rw [matrix_action, hi, word_zero, map_one]

/-- The three concrete conjugators used in the finite word certificates. -/
@[expose] public def localMat : Fin 3 → Mat :=
  ![![1, 2, 7, 9], ![1, 2, 5, 10], ![1, 3, 4, 12]]
/-- All eight matrices of the local conjugation image. -/
@[expose] public def localTable : Fin 8 → Mat :=
  ![![1, 2, 4, 8], ![1, 2, 5, 10], ![1, 2, 6, 11], ![1, 2, 7, 9],
    ![1, 3, 4, 12], ![1, 3, 5, 15], ![1, 3, 6, 13], ![1, 3, 7, 14]]

@[expose] public def localGen (i : Fin 3) : modelT :=
  ⟨![z 1 * z 2, z 3, b] i, by
    have h : ∀ i : Fin 3, ![z 1 * z 2, z 3, b] i ∈ modelT := by decide +kernel
    exact h i⟩

private theorem localGen_columns : ∀ j : Fin 3, ∀ i : Fin 4,
    localAction (localGen j) (word (basisIndex i)) = word (localMat j i) := by decide +kernel

public theorem matrix_localGen (j : Fin 3) : matrix (localAction (localGen j)) = localMat j :=
  (matrix_eq_iff _ _).mpr (localGen_columns j)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem localAction_columns : ∀ x : modelT, ∃ j : Fin 8,
    ∀ i : Fin 4, localAction x (word (basisIndex i)) = word (localTable j i) := by decide +kernel

public theorem localAction_range : localAction.range = localAutomizer := by
  apply le_antisymm
  · rintro f ⟨t, rfl⟩
    exact localAction_mem t
  · rintro f ⟨t, rfl⟩
    have ht : (t : TwistedModel) ∈ modelT := modelF_normalizer ▸ t.property
    exact ⟨⟨t, ht⟩, rfl⟩

public theorem matrix_of_mem_local (f : MulAut modelF) (hf : f ∈ localAutomizer) :
    ∃ j : Fin 8, matrix f = localTable j := by
  rw [← localAction_range] at hf
  obtain ⟨t, rfl⟩ := hf
  obtain ⟨j, hj⟩ := localAction_columns t
  exact ⟨j, (matrix_eq_iff _ _).mpr hj⟩

public theorem local_fixes_pointZ (f : MulAut modelF) (hf : f ∈ localAutomizer) :
    f pointZ = pointZ := by
  obtain ⟨j, hj⟩ := matrix_of_mem_local f hf
  have h := matrix_spec f 0
  change f (word 1) = word (matrix f 0) at h
  have ht : ∀ j : Fin 8, localTable j 0 = 1 := by decide +kernel
  simpa only [hj, ht, word_one] using h

/-- Matrix words are ordinary products in the three local actors and one new actor. -/
@[expose] public def generators (m : Mat) : Fin 4 → Mat :=
  ![localMat 0, localMat 1, localMat 2, m]
@[expose] public def evalMat (m : Mat) : List (Fin 4) → Mat
  | [] => basisIndex
  | i :: w => mmul (generators m i) (evalMat m w)

@[expose] public def autGenerators (f : MulAut modelF) : Fin 4 → MulAut modelF :=
  ![localAction (localGen 0), localAction (localGen 1), localAction (localGen 2), f]
@[expose] public def evalAut (f : MulAut modelF) : List (Fin 4) → MulAut modelF
  | [] => 1
  | i :: w => autGenerators f i * evalAut f w

public theorem matrix_autGenerators (f : MulAut modelF) (i : Fin 4) :
    matrix (autGenerators f i) = generators (matrix f) i := by
  fin_cases i
  · exact matrix_localGen 0
  · exact matrix_localGen 1
  · exact matrix_localGen 2
  · rfl

public theorem matrix_evalAut (f : MulAut modelF) (w : List (Fin 4)) :
    matrix (evalAut f w) = evalMat (matrix f) w := by
  induction w with
  | nil => exact matrix_one
  | cons i w ih =>
    change matrix (autGenerators f i * evalAut f w) = _
    rw [matrix_mul, matrix_autGenerators, ih]
    rfl

public theorem evalAut_mem (H : Subgroup (MulAut modelF)) (hlocal : localAutomizer ≤ H)
    (f : MulAut modelF) (hf : f ∈ H) (w : List (Fin 4)) : evalAut f w ∈ H := by
  have hg : ∀ i, autGenerators f i ∈ H := by
    intro i
    fin_cases i
    · exact hlocal (localAction_mem (localGen 0))
    · exact hlocal (localAction_mem (localGen 1))
    · exact hlocal (localAction_mem (localGen 2))
    · exact hf
  induction w with
  | nil => exact H.one_mem
  | cons i w ih => exact H.mul_mem (hg i) ih

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII.FAction.Identification
