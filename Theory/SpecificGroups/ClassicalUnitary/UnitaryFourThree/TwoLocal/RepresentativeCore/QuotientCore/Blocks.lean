module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.Quaternion
public import Mathlib.LinearAlgebra.UnitaryGroup
/-!
# Determinant-compatible blocks in the projective involution centralizer

Every special-unitary lift preserves or interchanges the two eigenspaces.
The two GU₂ blocks have determinant product one. Membership in the concrete
quaternion image is expressed using the full scalar kernel of SU₄ → PSU₄.
These interfaces support the quotient calculation, without using the larger
full-unitary block group's quotient.

The block extraction adapts `ElementaryLocal/InvolutionCentralizer/RepresentativeBound`.
Source conventions: GLS3, chapter 2, §2.7 (`refs/KGroup/GLS3/chapter2.tex`).
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore
@[expose] public section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.QuotientCore.Blocks
abbrev F := FiniteField.Nine
abbrev M (n : ℕ) := Matrix (Fin n) (Fin n) F
abbrev U (n : ℕ) := Matrix.unitaryGroup (Fin n) F
abbrev SU := (form 4).specialSubgroup
abbrev D := standardInvolutionMatrix
def swap : Mat₄ := !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]
theorem swap_sq : swap * swap = 1 := by decide
theorem star_swap : star swap = swap := by decide
theorem swap_anti : swap * D = -(D * swap) := by decide
theorem swap_det : swap.det = 1 := by decide
def top (A : M 4) : M 2 := fun i j => A (Fin.castAdd 2 i) (Fin.castAdd 2 j)
def bot (A : M 4) : M 2 := fun i j => A (Fin.natAdd 2 i) (Fin.natAdd 2 j)

theorem top_block (A B : M 2) : top (block A B) = A := by
  apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> rfl
theorem bot_block (A B : M 2) : bot (block A B) = B := by
  apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> rfl

theorem commute_shape (A : M 4) (h : A * D = D * A) : A = block (top A) (bot A) := by
  have hneg (x : FiniteField.Nine) : -x = x ↔ x = 0 := by revert x; decide
  have hneg' (x : FiniteField.Nine) : x = -x ↔ x = 0 := by revert x; decide
  have hh (i j : Fin 4) := congrArg (fun B : M 4 => B i j) h
  simp only [D, standardInvolutionMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul] at hh
  apply Matrix.ext; intro i j
  have hij := hh i j
  fin_cases i <;> fin_cases j <;>
    first | rfl | simpa [block, top, bot, hneg, hneg'] using hij


theorem commute_exists (g : U 4) (h : g.val * D = D * g.val) :
    ∃ A B : U 2, g.val = block A.val B.val := by
  have hs := commute_shape g.val h
  have hu := Matrix.mem_unitaryGroup_iff'.mp g.property
  rw [hs] at hu
  change (block (top g.val) (bot g.val)).conjTranspose * block (top g.val) (bot g.val) = 1 at hu
  rw [block_adj, block_mul, ← block_one] at hu
  have hA : top g.val ∈ Matrix.unitaryGroup (Fin 2) FiniteField.Nine := by
    rw [Matrix.mem_unitaryGroup_iff']
    change (top g.val).conjTranspose * top g.val = 1
    simpa only [top_block] using congrArg top hu
  have hB : bot g.val ∈ Matrix.unitaryGroup (Fin 2) FiniteField.Nine := by
    rw [Matrix.mem_unitaryGroup_iff']
    change (bot g.val).conjTranspose * bot g.val = 1
    simpa only [bot_block] using congrArg bot hu
  exact ⟨⟨top g.val, hA⟩, ⟨bot g.val, hB⟩, hs⟩

def swapUnitary : U 4 := ⟨swap, by rw [Matrix.mem_unitaryGroup_iff', star_swap, swap_sq]⟩
def matrixHom : SU →* Mat₄ := (Units.coeHom _).comp ((form 4).specialSubgroup.subtype)
theorem su_unitary (g : SU) : g.val.val.conjTranspose * g.val.val = 1 := by
  have h := ((form 4).mem_specialSubgroup_iff g.val).mp g.property |>.1
  change g.val.val.conjTranspose * 1 * g.val.val = 1 at h
  simpa only [mul_one] using h
theorem su_det (g : SU) : g.val.val.det = 1 := by
  have hd : Matrix.GeneralLinearGroup.det g.val = 1 :=
    (((form 4).mem_specialSubgroup_iff g.val).mp g.property).2
  have h := congrArg (fun u : Fˣ => u.val) hd
  simpa only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] using h
theorem su_inv (g : SU) : (g⁻¹).val.val = g.val.val.conjTranspose :=
  g.val.inv_eq_of_mul_eq_one_left (su_unitary g)

theorem signed_exists (g : SU) (hg : project 4 g ∈ standardCentralizer) :
    ∃ A B : U 2, A.val.det * B.val.det = 1 ∧
      (g.val.val = block A.val B.val ∨ g.val.val = block A.val B.val * swap) := by
  let u : U 4 := ⟨g.val.val, (Matrix.mem_unitaryGroup_iff').mpr (su_unitary g)⟩
  rcases (project_mem_standardCentralizer_iff g).mp hg with h | h
  · obtain ⟨A,B,he⟩ := commute_exists u h
    refine ⟨A,B,?_,Or.inl he⟩
    have hd := su_det g
    change u.val.det = 1 at hd
    rwa [he, block_det] at hd
  · have hh : (u * swapUnitary).val * D = D * (u * swapUnitary).val := by
      change (g.val.val * swap) * D = D * (g.val.val * swap)
      rw [mul_assoc, swap_anti, mul_neg, ← mul_assoc, h, neg_mul, neg_neg, mul_assoc]
    obtain ⟨A,B,he⟩ := commute_exists (u * swapUnitary) hh
    have he' : g.val.val = block A.val B.val * swap := by
      rw [← he]
      change g.val.val = (g.val.val * swap) * swap
      rw [mul_assoc, swap_sq, mul_one]
    refine ⟨A,B,?_,Or.inr he'⟩
    have hd := su_det g
    rwa [he', Matrix.det_mul, swap_det, mul_one, block_det] at hd

theorem swap_block (A B : Mat₂) : swap * block A B = block B A * swap := by
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;> simp [swap, block, Matrix.mul_apply, Fin.sum_univ_succ]
theorem block_pow (A B : Mat₂) (n : ℕ) : (block A B) ^ n = block (A ^ n) (B ^ n) := by
  induction n with
  | zero => exact block_one.symm
  | succ n hn => rw [pow_succ, hn, block_mul, ← pow_succ, ← pow_succ]
theorem block_smul (u : F) (A B : Mat₂) : block (u • A) (u • B) = u • block A B := by
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;> simp [block]

theorem mem_core_iff (g : SU) (hg : project 4 g ∈ standardCentralizer) :
    (⟨project 4 g, hg⟩ : standardCentralizer) ∈ quaternionCore ↔
      ∃ (q : QuaternionGroup 2 × QuaternionGroup 2) (u : Fˣ),
        g.val.val = u.val • block (quaternionMatrix q.1) (quaternionMatrix q.2) := by
  constructor
  · rintro ⟨q,hq⟩
    have he : ProjGenLinGroup.mk (quaternionPairSU q).val = ProjGenLinGroup.mk g.val :=
      congrArg (fun x : standardCentralizer => x.val.val) hq
    obtain ⟨u,hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp he
    refine ⟨q,u,?_⟩
    have hm := congrArg Units.val hu
    change block (quaternionMatrix q.1) (quaternionMatrix q.2) * Matrix.scalar (Fin 4) u.val =
      g.val.val at hm
    simpa only [Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal] using hm.symm
  · rintro ⟨q,u,hu⟩
    refine ⟨q, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change ProjGenLinGroup.mk (quaternionPairSU q).val = ProjGenLinGroup.mk g.val
    apply ProjGenLinGroup.mk_eq_mk_iff.mpr
    refine ⟨u, Units.ext ?_⟩
    change block (quaternionMatrix q.1) (quaternionMatrix q.2) * Matrix.scalar (Fin 4) u.val =
      g.val.val
    simpa only [Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal] using hu.symm
end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.RepresentativeCore.QuotientCore.Blocks
