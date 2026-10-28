module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.NonsingularImages.FourRows

/-!
# Exact subgroups in the three nonsingular non-box images

After retaining the original pair permutation, a subgroup of a whole (b), (c),
or (d) image is determined by a binary subspace of its three remaining
coordinates. A checked eight-coordinate subgroup law enumerates all sixteen
subspaces; explicit binary generators reconstruct the WHOLE subgroup.
This supplies the finite input for the exact-row refinement of KW Lemma 2.3.1.
Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), p.492.
-/

set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
@[expose] public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.NonsingularImages.Refinement
open Subgroup Theory.GroupTheory Cardinality.QuotientCount.Image Cardinality.KernelCount
open ElementaryEightGeometry
open scoped IsMulCommutative

def rawGenerator (r : Fin 3) (j : Fin 3) : StarGroup :=
  ![ElementaryEightGeometry.rowGenerator 0,
    fun j => NonsingularC.wholeGenerator (j.castLE (by decide)),
    ElementaryEightGeometry.rowGenerator 1] r j

def fullGenerator (r : Fin 3) (j : Fin 4) : StarGroup :=
  if h : j.val < 3 then rawGenerator r ⟨j.val,h⟩ else pairPermutation

def fullImage (r : Fin 3) : Subgroup StarGroup := closure (Set.range (fullGenerator r))

theorem fullImage_eq_sourceRow (r : Fin 3) : fullImage r = sourceRow r.succ := by
  fin_cases r
  · rfl
  · change closure (Set.range (fullGenerator 1)) = closure (Set.range NonsingularC.wholeGenerator)
    apply congrArg Subgroup.closure
    apply congrArg Set.range
    funext j
    fin_cases j <;> rfl
  · rfl

private def generatorPoint : Fin 3 → Fin 3 → Fin 24 → Fin 24 :=
![![![0, 1, 3, 2, 5, 4, 6, 16, 14, 22, 18, 11, 12, 13, 8, 17, 7, 15, 10, 20, 19, 21, 9, 23], ![0, 1, 2, 3, 8, 14, 23, 15, 4, 22, 18, 11, 12, 21, 5, 7, 17, 16, 10, 19, 20, 13, 9, 6], ![0, 1, 2, 3, 16, 7, 23, 5, 17, 22, 10, 12, 11, 13, 15, 14, 4, 8, 18, 20, 19, 21, 9, 6]], ![![0, 1, 3, 2, 5, 4, 6, 16, 14, 22, 18, 11, 12, 13, 8, 17, 7, 15, 10, 20, 19, 21, 9, 23], ![0, 1, 19, 20, 14, 8, 6, 15, 5, 18, 22, 11, 12, 13, 4, 7, 17, 16, 9, 2, 3, 21, 10, 23], ![0, 1, 18, 10, 7, 16, 6, 4, 17, 19, 3, 11, 12, 13, 15, 14, 5, 8, 2, 9, 22, 21, 20, 23]], ![![0, 1, 3, 2, 5, 4, 6, 16, 14, 22, 18, 11, 12, 13, 8, 17, 7, 15, 10, 20, 19, 21, 9, 23], ![0, 1, 20, 19, 4, 5, 23, 16, 8, 18, 22, 11, 12, 21, 14, 17, 7, 15, 9, 3, 2, 13, 10, 6], ![0, 1, 10, 18, 4, 5, 23, 7, 14, 19, 2, 12, 11, 13, 8, 17, 16, 15, 3, 9, 22, 21, 20, 6]]]
private def generatorPermutation (r : Fin 3) (j : Fin 3) : Equiv.Perm (Fin 24) where
  toFun := generatorPoint r j
  invFun := generatorPoint r j
  left_inv := by revert r j; decide +kernel
  right_inv := by revert r j; decide +kernel

private theorem generator_val : ∀ r j, (rawGenerator r j).val = generatorPermutation r j := by
  decide +kernel

private theorem raw_square (r : Fin 3) (j : Fin 3) : rawGenerator r j * rawGenerator r j = 1 := by
  apply Subtype.ext
  change (rawGenerator r j).val * (rawGenerator r j).val = 1
  rw [generator_val]
  revert r j
  decide +kernel
private theorem raw_commute (r : Fin 3) (i j : Fin 3) : Commute (rawGenerator r i) (rawGenerator r j) := by
  apply Subtype.ext
  change (rawGenerator r i).val * (rawGenerator r j).val = (rawGenerator r j).val * (rawGenerator r i).val
  rw [generator_val,generator_val]
  revert r i j
  decide +kernel
private theorem full_square (r : Fin 3) (j : Fin 4) : fullGenerator r j * fullGenerator r j = 1 := by
  apply Subtype.ext
  revert r j
  decide +kernel
private theorem full_commute (r : Fin 3) (i j : Fin 4) : Commute (fullGenerator r i) (fullGenerator r j) := by
  apply Subtype.ext
  revert r i j
  decide +kernel

def rawElement (r : Fin 3) (i : Fin 8) : StarGroup :=
  binaryProduct (rawGenerator r) (fun j => i.val.testBit j.val)

private def rawPoint : Fin 3 → Fin 8 → Fin 24 → Fin 24 :=
![![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23], ![0, 1, 3, 2, 5, 4, 6, 16, 14, 22, 18, 11, 12, 13, 8, 17, 7, 15, 10, 20, 19, 21, 9, 23], ![0, 1, 2, 3, 8, 14, 23, 15, 4, 22, 18, 11, 12, 21, 5, 7, 17, 16, 10, 19, 20, 13, 9, 6], ![0, 1, 3, 2, 14, 8, 23, 17, 5, 9, 10, 11, 12, 21, 4, 16, 15, 7, 18, 20, 19, 13, 22, 6], ![0, 1, 2, 3, 16, 7, 23, 5, 17, 22, 10, 12, 11, 13, 15, 14, 4, 8, 18, 20, 19, 21, 9, 6], ![0, 1, 3, 2, 7, 16, 23, 4, 15, 9, 18, 12, 11, 13, 17, 8, 5, 14, 10, 19, 20, 21, 22, 6], ![0, 1, 2, 3, 17, 15, 6, 14, 16, 9, 18, 12, 11, 21, 7, 5, 8, 4, 10, 20, 19, 13, 22, 23], ![0, 1, 3, 2, 15, 17, 6, 8, 7, 22, 10, 12, 11, 21, 16, 4, 14, 5, 18, 19, 20, 13, 9, 23]], ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23], ![0, 1, 3, 2, 5, 4, 6, 16, 14, 22, 18, 11, 12, 13, 8, 17, 7, 15, 10, 20, 19, 21, 9, 23], ![0, 1, 19, 20, 14, 8, 6, 15, 5, 18, 22, 11, 12, 13, 4, 7, 17, 16, 9, 2, 3, 21, 10, 23], ![0, 1, 20, 19, 8, 14, 6, 17, 4, 10, 9, 11, 12, 13, 5, 16, 15, 7, 22, 3, 2, 21, 18, 23], ![0, 1, 18, 10, 7, 16, 6, 4, 17, 19, 3, 11, 12, 13, 15, 14, 5, 8, 2, 9, 22, 21, 20, 23], ![0, 1, 10, 18, 16, 7, 6, 5, 15, 20, 2, 11, 12, 13, 17, 8, 4, 14, 3, 22, 9, 21, 19, 23], ![0, 1, 9, 22, 15, 17, 6, 14, 16, 2, 20, 11, 12, 13, 7, 4, 8, 5, 19, 18, 10, 21, 3, 23], ![0, 1, 22, 9, 17, 15, 6, 8, 7, 3, 19, 11, 12, 13, 16, 5, 14, 4, 20, 10, 18, 21, 2, 23]], ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23], ![0, 1, 3, 2, 5, 4, 6, 16, 14, 22, 18, 11, 12, 13, 8, 17, 7, 15, 10, 20, 19, 21, 9, 23], ![0, 1, 20, 19, 4, 5, 23, 16, 8, 18, 22, 11, 12, 21, 14, 17, 7, 15, 9, 3, 2, 13, 10, 6], ![0, 1, 19, 20, 5, 4, 23, 7, 14, 10, 9, 11, 12, 21, 8, 15, 16, 17, 22, 2, 3, 13, 18, 6], ![0, 1, 10, 18, 4, 5, 23, 7, 14, 19, 2, 12, 11, 13, 8, 17, 16, 15, 3, 9, 22, 21, 20, 6], ![0, 1, 18, 10, 5, 4, 23, 16, 8, 20, 3, 12, 11, 13, 14, 15, 7, 17, 2, 22, 9, 21, 19, 6], ![0, 1, 22, 9, 4, 5, 6, 16, 14, 3, 20, 12, 11, 21, 8, 15, 7, 17, 19, 18, 10, 13, 2, 23], ![0, 1, 9, 22, 5, 4, 6, 7, 8, 2, 19, 12, 11, 21, 14, 17, 16, 15, 20, 10, 18, 13, 3, 23]]]
private theorem rawElement_apply (r : Fin 3) (i : Fin 8) (x : Fin 24) :
    (rawElement r i).val x = rawPoint r i x := by
  change StarGroup.subtype (binaryProduct (rawGenerator r) (fun j => i.val.testBit j.val)) x = _
  rw [map_binaryProduct]
  simp only [subtype_apply,generator_val]
  revert r i x
  decide +kernel

theorem rawElement_zero (r : Fin 3) : rawElement r 0 = 1 := by
  exact binaryProduct_zero (rawGenerator r)

theorem rawElement_mul (r : Fin 3) (i j : Fin 8) :
    rawElement r i * rawElement r j = rawElement r (i ^^^ j) := by
  rw [rawElement,rawElement,binaryProduct_mul _ (raw_square r) (raw_commute r),rawElement]
  congr 1
  revert i j
  decide +kernel

private theorem full_product (r : Fin 3) (v : Fin 4 → Bool) :
    ∃ i : Fin 8, binaryProduct (fullGenerator r) v =
      rawElement r i * (if v 3 then pairPermutation else 1) := by
  have hb : ∀ v : Fin 3 → Bool, ∃ i : Fin 8, (fun j : Fin 3 => i.val.testBit j.val) = v := by
    decide +kernel
  obtain ⟨i,hi⟩ := hb (fun j => v (j.castLE (by decide)))
  refine ⟨i,?_⟩
  unfold rawElement
  rw [hi]
  simp only [binaryProduct, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    fullGenerator, Fin.val_zero, Fin.val_succ, show (0 : ℕ) < 3 by decide,
    show (1 : ℕ) < 3 by decide, show (2 : ℕ) < 3 by decide,
    show ¬(3 : ℕ) < 3 by decide, dite_true,dite_false,mul_one]
  simp only [mul_assoc]
  rfl

theorem mem_fullImage_iff (r : Fin 3) (x : StarGroup) :
    x ∈ fullImage r ↔ ∃ (i : Fin 8) (b : Bool),
      rawElement r i * (if b then pairPermutation else 1) = x := by
  constructor
  · intro hx
    obtain ⟨v,rfl⟩ := (mem_closure_iff_binaryProduct _ (full_square r) (full_commute r) x).mp hx
    obtain ⟨i,hi⟩ := full_product r v
    exact ⟨i,v 3,hi.symm⟩
  · rintro ⟨i,b,rfl⟩
    apply (fullImage r).mul_mem
    · exact binaryProduct_mem _ _ _ (fun j => subset_closure ⟨j.castLE (by decide),by
        simp [fullGenerator,j.isLt]⟩)
    · cases b
      · exact one_mem _
      · exact subset_closure ⟨3,rfl⟩

def spaceMask : Fin 16 → ℕ := ![1, 3, 5, 9, 17, 33, 65, 129, 15, 51, 195, 85, 165, 153, 105, 255]
def spaceBasis : Fin 16 → Fin 3 → Fin 8 := ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0], ![4, 0, 0], ![5, 0, 0], ![6, 0, 0], ![7, 0, 0], ![1, 2, 0], ![1, 4, 0], ![1, 6, 0], ![2, 4, 0], ![2, 5, 0], ![3, 4, 0], ![3, 5, 0], ![1, 2, 4]]
private def spanIndex (s : Fin 16) (i : Fin 8) : Fin 8 :=
  (if i.val.testBit 0 then spaceBasis s 0 else 0) ^^^
  ((if i.val.testBit 1 then spaceBasis s 1 else 0) ^^^
    (if i.val.testBit 2 then spaceBasis s 2 else 0))

private theorem space_span : ∀ (s : Fin 16) (i : Fin 8),
    (spaceMask s).testBit i.val = true ↔ ∃ j : Fin 8, spanIndex s j = i := by decide +kernel
private theorem basis_mem : ∀ (s : Fin 16) (j : Fin 3),
    (spaceMask s).testBit (spaceBasis s j).val = true := by decide +kernel

private theorem subgroup_test : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    let f : Fin 8 → Bool := ![b0,b1,b2,b3,b4,b5,b6,b7]
    f 0 = true → (∀ i j, f i = true → f j = true → f (i ^^^ j) = true) →
      ∃ s : Fin 16, ∀ i, f i = (spaceMask s).testBit i.val := by decide +kernel

private theorem subgroup_spaces (f : Fin 8 → Bool) (h0 : f 0 = true)
    (hm : ∀ i j, f i = true → f j = true → f (i ^^^ j) = true) :
    ∃ s : Fin 16, ∀ i, f i = (spaceMask s).testBit i.val := by
  have he : (![f 0,f 1,f 2,f 3,f 4,f 5,f 6,f 7] : Fin 8 → Bool) = f := by
    funext i; fin_cases i <;> rfl
  have h := subgroup_test (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7)
  dsimp only at h
  rw [he] at h
  exact h h0 hm

def spaceGenerator (r : Fin 3) (s : Fin 16) (j : Fin 4) : StarGroup :=
  if h : j.val < 3 then rawElement r (spaceBasis s ⟨j.val,h⟩) else pairPermutation

def spaceGroup (r : Fin 3) (s : Fin 16) : Subgroup StarGroup :=
  closure (Set.range (spaceGenerator r s))

private theorem raw_mem_space (r : Fin 3) (s : Fin 16) (i : Fin 8)
    (hi : (spaceMask s).testBit i.val = true) : rawElement r i ∈ spaceGroup r s := by
  obtain ⟨j,rfl⟩ := (space_span s i).mp hi
  have hb (b : Bool) (k : Fin 3) :
      rawElement r (if b then spaceBasis s k else 0) ∈ spaceGroup r s := by
    cases b
    · change rawElement r 0 ∈ spaceGroup r s
      rw [rawElement_zero]; exact one_mem _
    · exact subset_closure ⟨k.castLE (by decide),by simp [spaceGenerator,k.isLt]⟩
  rw [spanIndex,← rawElement_mul,← rawElement_mul]
  exact (spaceGroup r s).mul_mem (hb _ 0) ((spaceGroup r s).mul_mem (hb _ 1) (hb _ 2))

/-- Every subgroup of one of the three non-box containers containing the
original marked pair is one of the sixteen explicit binary subspace lifts. -/
theorem subgroup_exact_space (A : Subgroup StarGroup) (r : Fin 3)
    (hA : A ≤ fullImage r) (hp : pairPermutation ∈ A) :
    ∃ s : Fin 16, A = spaceGroup r s := by
  classical
  let f : Fin 8 → Bool := fun i => decide (rawElement r i ∈ A)
  have h0 : f 0 = true := by simp [f,rawElement_zero]
  have hm : ∀ i j, f i = true → f j = true → f (i ^^^ j) = true := by
    intro i j hi hj
    apply decide_eq_true
    rw [← rawElement_mul]
    exact A.mul_mem (of_decide_eq_true hi) (of_decide_eq_true hj)
  obtain ⟨s,hs⟩ := subgroup_spaces f h0 hm
  have iff_mem (i : Fin 8) : rawElement r i ∈ A ↔ (spaceMask s).testBit i.val = true := by
    rw [← hs i]
    exact (decide_eq_true_iff).symm
  refine ⟨s,le_antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨i,b,rfl⟩ := (mem_fullImage_iff r x).mp (hA hx)
    have hi : rawElement r i ∈ A := by
      cases b
      · simpa using hx
      · have h := A.mul_mem hx (A.inv_mem hp)
        simpa only [ite_true,mul_inv_cancel_right] using h
    apply (spaceGroup r s).mul_mem (raw_mem_space r s i ((iff_mem i).mp hi))
    cases b
    · exact one_mem _
    · exact subset_closure ⟨3,rfl⟩
  · apply (closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    unfold spaceGenerator
    split_ifs with hj
    · exact (iff_mem _).mpr (basis_mem s ⟨j.val,hj⟩)
    · exact hp

end Janko4.LocalStructure.ElementaryNormalizerCover.NonsingularImages.Refinement
