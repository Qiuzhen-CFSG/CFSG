module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.KernelCompletion.Checks.Predicates

/-!
# Sequential certificates for the element, completion, and scalar pairing

Traverse the four summand/output row lists together to identify I+A+B+BAB,
and traverse the element/completion lists together to add the fixed outer
product. The soundness proofs recover each literal array entry by induction.
This avoids repeatedly indexing the large arrays in the sum checker.
The two remaining scalar identities use the already-proved packed arithmetic.
Source and measurements: `../source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.KernelCompletion.Checks

def sumListCheck : ℕ → List ℕ → List ℕ → List ℕ → List ℕ → Bool
  | k, a :: as, b :: bs, c :: cs, d :: ds =>
      ((2 ^ k ^^^ a ^^^ b ^^^ c) == d) && sumListCheck (k+1) as bs cs ds
  | _, [], [], [], [] => true
  | _, _, _, _, _ => false

theorem sumListCheck_sound (k : ℕ) (as bs cs ds : List ℕ)
    (h : sumListCheck k as bs cs ds = true) (i : ℕ) (hi : i < ds.length) :
    (2 ^ (k+i) ^^^ as[i]! ^^^ bs[i]! ^^^ cs[i]!) = ds[i]! := by
  induction ds generalizing k as bs cs i with
  | nil => simp at hi
  | cons d ds ih =>
    cases as with
    | nil => simp [sumListCheck] at h
    | cons a as =>
      cases bs with
      | nil => simp [sumListCheck] at h
      | cons b bs =>
        cases cs with
        | nil => simp [sumListCheck] at h
        | cons c cs =>
          simp only [sumListCheck, Bool.and_eq_true, beq_iff_eq] at h
          cases i with
          | zero => simpa using h.1
          | succ i =>
            have hh := ih (k+1) as bs cs h.2 i (by simpa using hi)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

def completionListCheck (u v : ℕ) : ℕ → List ℕ → List ℕ → Bool
  | k, d :: ds, c :: cs =>
      ((d ^^^ (if u.testBit k then v else 0)) == c) && completionListCheck u v (k+1) ds cs
  | _, [], [] => true
  | _, _, _ => false

theorem completionListCheck_sound (u v k : ℕ) (ds cs : List ℕ)
    (h : completionListCheck u v k ds cs = true) (i : ℕ) (hi : i < cs.length) :
    (ds[i]! ^^^ (if u.testBit (k+i) then v else 0)) = cs[i]! := by
  induction cs generalizing k ds i with
  | nil => simp at hi
  | cons c cs ih =>
    cases ds with
    | nil => simp [completionListCheck] at h
    | cons d ds =>
      simp only [completionListCheck, Bool.and_eq_true, beq_iff_eq] at h
      cases i with
      | zero => simpa using h.1
      | succ i =>
        have hh := ih (k+1) ds h.2 i (by simpa using hi)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

set_option maxRecDepth 8192 in
theorem sum_list_check : sumListCheck 0 Data1242.firstRows.toList
    Data1242.secondRows.toList Data.babRows.toList Data.elementRows.toList = true := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem completion_list_check : completionListCheck columnPacked rowPacked 0
    Data.elementRows.toList Data.completedRows.toList = true := by
  decide +kernel

theorem element_row (i : Fin 1242) :
    (2 ^ i.val ^^^ Data1242.firstRows[i.val]! ^^^ Data1242.secondRows[i.val]! ^^^
      Data.babRows[i.val]!) = Data.elementRows[i.val]! := by
  have hh := sumListCheck_sound 0 Data1242.firstRows.toList Data1242.secondRows.toList
    Data.babRows.toList Data.elementRows.toList sum_list_check i.val
    (by simpa only [Array.length_toList, element_size] using i.isLt)
  simpa only [Nat.zero_add, Array.getElem!_toList] using hh

theorem completion_row (i : Fin 1242) :
    (Data.elementRows[i.val]! ^^^ (if columnPacked.testBit i.val then rowPacked else 0)) =
      Data.completedRows[i.val]! := by
  have hh := completionListCheck_sound columnPacked rowPacked 0 Data.elementRows.toList
    Data.completedRows.toList completion_list_check i.val
    (by simpa only [Array.length_toList, completed_size] using i.isLt)
  simpa only [Nat.zero_add, Array.getElem!_toList] using hh

theorem element_check : checkRange elementCheck 0 1242 = true := by
  unfold checkRange
  apply List.all_eq_true.mpr
  intro i hi
  have hi' : i < 1242 := by
    obtain ⟨j, hj, rfl⟩ := List.mem_range'.mp hi
    omega
  exact beq_iff_eq.mpr (element_row ⟨i, hi'⟩)

theorem completion_check : checkRange completionCheck 0 1242 = true := by
  unfold checkRange
  apply List.all_eq_true.mpr
  intro i hi
  have hi' : i < 1242 := by
    obtain ⟨j, hj, rfl⟩ := List.mem_range'.mp hi
    omega
  exact beq_iff_eq.mpr (completion_row ⟨i, hi'⟩)

set_option maxRecDepth 8192 in
theorem row_check : packedMul rowPacked Data.elementRows.toList 0 = 0 := by decide +kernel

set_option maxRecDepth 8192 in
theorem pairing_check : packedDot rowPacked columnPacked 1242 = 1 := by decide +kernel
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.KernelCompletion.Checks
