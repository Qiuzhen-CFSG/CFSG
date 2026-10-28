module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.BoxTetrads

/-!
# Exact fixed-point-containing subgroups of the native box

The five literal box generators give binary coordinates. Retaining the marked
pair reduces subgroup enumeration to four coordinates. Six coordinates yield a
fixed-point-free element after multiplication by the pair; removing them leaves
sixteen subspaces, certified by the binary subgroup law. Eight have the common
fixed tetrad treated by `BoxTetrads`; the other eight remain explicit residual
images. The statement is about the existing native permutation generators and
does not assume a complete printed Golay-coordinate identification.

Source motivation: Kleidman--Wilson (1988), Figure 2(a), Lemma 2.3.1 and
Proposition 2.3.2, p.492. This refinement does not classify the normalizers of
the eight residual images.
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryNormalizerCover.BoxImages
open Cardinality.QuotientCount.Image Cardinality.KernelCount ElementaryEightGeometry
open NonsingularImages

def rawGenerator (j : Fin 4) : StarGroup := FigureA.wholeGenerator (j.castLE (by decide))
def rawElement (i : Fin 16) : StarGroup :=
  binaryProduct rawGenerator (fun j => i.val.testBit j.val)

private theorem full_square (j : Fin 5) : FigureA.wholeGenerator j * FigureA.wholeGenerator j = 1 := by
  apply Subtype.ext
  revert j
  decide +kernel
private theorem full_commute (i j : Fin 5) : Commute (FigureA.wholeGenerator i) (FigureA.wholeGenerator j) := by
  apply Subtype.ext
  revert i j
  decide +kernel

theorem raw_zero : rawElement 0 = 1 := binaryProduct_zero rawGenerator
theorem raw_mul (i j : Fin 16) : rawElement i * rawElement j = rawElement (i ^^^ j) := by
  have hs (k : Fin 4) : rawGenerator k * rawGenerator k = 1 := full_square _
  have hc (k l : Fin 4) : Commute (rawGenerator k) (rawGenerator l) := full_commute _ _
  rw [rawElement,rawElement,binaryProduct_mul rawGenerator hs hc,rawElement]
  congr 1
  revert i j
  decide +kernel

private theorem full_product (v : Fin 5 → Bool) :
    ∃ i : Fin 16, binaryProduct FigureA.wholeGenerator v =
      rawElement i * (if v 4 then pairPermutation else 1) := by
  have hb : ∀ v : Fin 4 → Bool, ∃ i : Fin 16, (fun j : Fin 4 => i.val.testBit j.val) = v := by
    decide +kernel
  obtain ⟨i,hi⟩ := hb (fun j => v (j.castLE (by decide)))
  refine ⟨i,?_⟩
  unfold rawElement
  rw [hi]
  simp only [binaryProduct,List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_nil,
    mul_one,rawGenerator]
  simp only [mul_assoc]
  rfl

theorem mem_box_iff (x : StarGroup) : x ∈ boxImage ↔
    ∃ (i : Fin 16) (b : Bool), rawElement i * (if b then pairPermutation else 1) = x := by
  constructor
  · intro hx
    obtain ⟨v,rfl⟩ := (mem_closure_iff_binaryProduct _ full_square full_commute x).mp hx
    obtain ⟨i,hi⟩ := full_product v
    exact ⟨i,v 4,hi.symm⟩
  · rintro ⟨i,b,rfl⟩
    apply boxImage.mul_mem
    · exact binaryProduct_mem _ _ _ (fun j => FigureA.wholeGenerator_mem _)
    · cases b
      · exact one_mem _
      · exact FigureA.wholeGenerator_mem 4

private def forbidden : Fin 16 → Bool :=
  ![false,false,false,false,true,true,false,false,true,false,true,false,true,false,false,true]
private theorem forbidden_free : ∀ (i : Fin 16), forbidden i = true →
    ∀ j : Fin 24, (rawElement i * pairPermutation).val j ≠ j := by decide +kernel

def spaceMask : Fin 16 → ℕ :=
  ![1,3,5,9,15,195,2565,24585,65,129,513,2049,8193,16385,10305,17025]
def spaceBasis : Fin 16 → Fin 2 → Fin 16 :=
  ![![0,0],![1,0],![2,0],![3,0],![1,2],![1,6],![2,9],![3,13],
    ![6,0],![7,0],![9,0],![11,0],![13,0],![14,0],![6,11],![7,9]]

private def spanIndex (s : Fin 16) (i : Fin 4) : Fin 16 :=
  (if i.val.testBit 0 then spaceBasis s 0 else 0) ^^^
    (if i.val.testBit 1 then spaceBasis s 1 else 0)
private theorem space_span : ∀ (s : Fin 16) (i : Fin 16),
    (spaceMask s).testBit i.val = true ↔ ∃ j : Fin 4, spanIndex s j = i := by decide +kernel
private theorem basis_mem : ∀ (s : Fin 16) (j : Fin 2),
    (spaceMask s).testBit (spaceBasis s j).val = true := by decide +kernel

private theorem subgroup_test : ∀ b1 b2 b3 b6 b7 b9 b11 b13 b14 : Bool,
    let f : Fin 16 → Bool :=
      ![true,b1,b2,b3,false,false,b6,b7,false,b9,false,b11,false,b13,b14,false]
    (∀ i j, f i = true → f j = true → f (i ^^^ j) = true) →
      ∃ s : Fin 16, ∀ i, f i = (spaceMask s).testBit i.val := by decide +kernel

private theorem subgroup_spaces (f : Fin 16 → Bool) (h0 : f 0 = true)
    (hm : ∀ i j, f i = true → f j = true → f (i ^^^ j) = true)
    (hb : ∀ i, forbidden i = true → f i = false) :
    ∃ s : Fin 16, ∀ i, f i = (spaceMask s).testBit i.val := by
  have he : (![true,f 1,f 2,f 3,false,false,f 6,f 7,false,f 9,false,f 11,false,f 13,f 14,false] :
      Fin 16 → Bool) = f := by
    funext i
    fin_cases i <;> first | exact h0.symm | exact (hb _ rfl).symm | rfl
  have h := subgroup_test (f 1) (f 2) (f 3) (f 6) (f 7) (f 9) (f 11) (f 13) (f 14)
  dsimp only at h
  rw [he] at h
  exact h hm

def spaceGenerator (s : Fin 16) : Fin 3 → StarGroup :=
  ![pairPermutation,rawElement (spaceBasis s 0),rawElement (spaceBasis s 1)]
def spaceGroup (s : Fin 16) : Subgroup StarGroup := closure (Set.range (spaceGenerator s))

private theorem raw_mem_space (s : Fin 16) (i : Fin 16)
    (hi : (spaceMask s).testBit i.val = true) : rawElement i ∈ spaceGroup s := by
  obtain ⟨j,rfl⟩ := (space_span s i).mp hi
  have hb (b : Bool) (k : Fin 2) :
      rawElement (if b then spaceBasis s k else 0) ∈ spaceGroup s := by
    cases b
    · change rawElement 0 ∈ spaceGroup s
      rw [raw_zero]; exact one_mem _
    · have he : spaceGenerator s k.succ = rawElement (spaceBasis s k) := by
        fin_cases k <;> rfl
      exact subset_closure ⟨k.succ,he⟩
  rw [spanIndex,← raw_mul]
  exact (spaceGroup s).mul_mem (hb _ 0) (hb _ 1)

theorem subgroup_exact_space (A : Subgroup StarGroup) (hA : A ≤ boxImage)
    (hp : pairPermutation ∈ A)
    (hfixed : ∀ p ∈ A, ∃ i : Fin 24, p.val i = i) :
    ∃ s : Fin 16, A = spaceGroup s := by
  classical
  let f : Fin 16 → Bool := fun i => decide (rawElement i ∈ A)
  have h0 : f 0 = true := by simp [f,raw_zero]
  have hm : ∀ i j, f i = true → f j = true → f (i ^^^ j) = true := by
    intro i j hi hj
    apply decide_eq_true
    rw [← raw_mul]
    exact A.mul_mem (of_decide_eq_true hi) (of_decide_eq_true hj)
  have hb (i : Fin 16) (hi : forbidden i = true) : f i = false := by
    apply decide_eq_false
    intro hm
    obtain ⟨j,hj⟩ := hfixed _ (A.mul_mem hm hp)
    exact forbidden_free i hi j hj
  obtain ⟨s,hs⟩ := subgroup_spaces f h0 hm hb
  have iff_mem (i : Fin 16) : rawElement i ∈ A ↔ (spaceMask s).testBit i.val = true := by
    rw [← hs i]
    exact (decide_eq_true_iff).symm
  refine ⟨s,le_antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨i,b,rfl⟩ := (mem_box_iff x).mp (hA hx)
    have hi : rawElement i ∈ A := by
      cases b
      · simpa using hx
      · have h := A.mul_mem hx (A.inv_mem hp)
        simpa only [ite_true,mul_inv_cancel_right] using h
    apply (spaceGroup s).mul_mem (raw_mem_space s i ((iff_mem i).mp hi))
    cases b
    · exact one_mem _
    · exact subset_closure ⟨0,rfl⟩
  · apply (closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    fin_cases j
    · exact hp
    · exact (iff_mem _).mpr (basis_mem s 0)
    · exact (iff_mem _).mpr (basis_mem s 1)

def residualImage (r : Fin 8) : Subgroup StarGroup := spaceGroup (r.castLE (by decide))

private theorem tetrad_generator (r : Fin 8) (j : Fin 3) :
    spaceGenerator ⟨r.val+8,by omega⟩ j = BoxTetrads.rowGenerator r j := by
  apply Subtype.ext
  revert r j
  decide +kernel

theorem subgroup_residual_or_tetrad (A : Subgroup StarGroup) (hA : A ≤ boxImage)
    (hp : pairPermutation ∈ A)
    (hfixed : ∀ p ∈ A, ∃ i : Fin 24, p.val i = i) :
    (∃ r : Fin 8, A = residualImage r) ∨ ∃ r : Fin 8, A = BoxTetrads.rowImage r := by
  obtain ⟨s,rfl⟩ := subgroup_exact_space A hA hp hfixed
  by_cases hs : s.val < 8
  · exact Or.inl ⟨⟨s.val,hs⟩,rfl⟩
  · let r : Fin 8 := ⟨s.val-8,by omega⟩
    have he : s = ⟨r.val+8,by omega⟩ := Fin.ext (by dsimp [r]; omega)
    refine Or.inr ⟨r,?_⟩
    rw [he]
    apply congrArg Subgroup.closure
    apply congrArg Set.range
    funext j
    exact tetrad_generator r j

end Janko4.LocalStructure.ElementaryNormalizerCover.BoxImages
