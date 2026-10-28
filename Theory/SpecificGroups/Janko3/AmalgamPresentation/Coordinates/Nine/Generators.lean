module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.Basic
public import Theory.GroupTheory.CosetWordCertificate
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.FinCases

/-!
# Generation in the exact third-local coordinates

Explicit checked words produce both complete root groups, every diagonal
class, and the pure cubic kernel. They generate `3 : PGL₂(9)` with the
literal pair from the model-coordinate discovery. The search supplies no
premise: matrix entries and cubic coordinates are checked in Lean.
-/

@[expose] public section
set_option Elab.async false
namespace Sporadic.Janko3.AmalgamPresentation.NineCoordinates
open Subgroup Subgroup.CosetWordCertificate

private def generator : Bool → ComputableModel := fun b => if b then second else first
private noncomputable def canonicalGenerator : Bool → Canonical := fun b => if b then canonicalSecond else canonicalFirst
private theorem eval_hom {A B α : Type*} [Group A] [Group B]
    (f : A →* B) (g : α → A) (w : Word α) :
    f (eval g w) = eval (fun i => f (g i)) w := by
  induction w with
  | nil => simp only [eval_nil,map_one]
  | cons a w ih =>
    cases ha : a.2 <;> simp only [eval_cons,ha,Bool.false_eq_true,↓reduceIte,map_mul,map_inv,ih]

private theorem map_eval (w : Word Bool) :
    toCanonical (eval generator w) = eval canonicalGenerator w := by
  have he : (fun b => toCanonical (generator b)) = canonicalGenerator := by
    funext b
    cases b <;> rfl
  exact (eval_hom toCanonical generator w).trans (congrArg (fun g => eval g w) he)

private def fieldElement : Fin 9 → F
  | 0 => ⟨0,0⟩
  | 1 => ⟨1,0⟩
  | 2 => ⟨2,0⟩
  | 3 => ⟨0,1⟩
  | 4 => ⟨1,1⟩
  | 5 => ⟨2,1⟩
  | 6 => ⟨0,2⟩
  | 7 => ⟨1,2⟩
  | _ => ⟨2,2⟩
private theorem fieldElement_surjective : Function.Surjective fieldElement := by
  change ∀ x : F, ∃ i : Fin 9, fieldElement i = x
  decide +kernel
private def unitElement (i : Fin 8) : Fˣ := Units.mk0 (fieldElement ⟨i.val+1,by omega⟩) (by
  have h : ∀ i : Fin 8, fieldElement ⟨i.val+1,by omega⟩ ≠ 0 := by decide +kernel
  exact h i)
private theorem unitElement_surjective : Function.Surjective unitElement := by
  intro x
  obtain ⟨i,hi⟩ := fieldElement_surjective (x : F)
  have hi0 : i.val ≠ 0 := by
    intro hz
    have he : i = 0 := Fin.ext hz
    subst i
    have hf : fieldElement 0 = 0 := by decide +kernel
    exact x.ne_zero (hi.symm.trans hf)
  refine ⟨⟨i.val-1,by omega⟩,?_⟩
  apply Units.ext
  change fieldElement ⟨i.val-1+1,by omega⟩ = x
  have he : (⟨i.val-1+1,by omega⟩ : Fin 9) = i := Fin.ext (by change i.val-1+1 = i.val; omega)
  rw [he]
  exact hi

private def diagonal (d : Fˣ) : GL9 := Matrix.GeneralLinearGroup.mkOfDetNeZero
  !![(d:F),0;0,1] (by simp [Matrix.det_fin_two,d.ne_zero])
private theorem diagonal_det (d : Fˣ) : (diagonal d).det = d := by
  apply Units.ext
  simp [diagonal,Matrix.det_fin_two]

private def checkFin {n : Nat} (f : Fin n → Bool) : Bool :=
  (List.range n).all (fun i => if h : i < n then f ⟨i,h⟩ else true)
private theorem allFin {n : Nat} (P : Fin n → Prop) [DecidablePred P]
    (h : checkFin (fun i => decide (P i)) = true) : ∀ i, P i := by
  intro i
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt,decide_eq_true_eq] using hi

private theorem projective_scalar (g : ComputableModel) (a : Z) (m : GL9) (u : Fˣ)
    (ha : g.left = a) (hm : g.right = Matrix.GeneralLinearGroup.scalar (Fin 2) u * m) :
    toCanonical g = ⟨a,Matrix.ProjGenLinGroup.mk m⟩ := by
  apply SemidirectProduct.ext
  · exact ha
  · change Matrix.ProjGenLinGroup.mk g.right = _
    rw [hm,map_mul,Matrix.ProjGenLinGroup.mk_scalar,one_mul]

private def upperWord : Fin 9 → Word Bool
  | 0 => []
  | 1 => [(false, true), (false, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (true, true), (true, true), (true, true), (true, true)]
  | 2 => [(true, true), (false, true), (false, true), (true, true), (false, true), (false, true), (true, true), (true, true), (true, true), (true, true)]
  | 3 => [(false, true), (false, true), (false, true), (false, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true)]
  | 4 => [(true, true), (false, true), (false, true), (false, true), (true, true), (true, true), (true, true), (false, true), (true, true), (false, true), (true, true), (true, true)]
  | 5 => [(false, true), (true, true), (false, true), (false, true), (false, true), (true, true), (false, true), (false, true), (false, true), (false, true), (false, true), (true, true)]
  | 6 => [(false, true), (false, true), (true, true), (false, true), (true, true), (false, true), (false, true), (false, true), (true, true), (true, true), (true, true), (false, true)]
  | 7 => [(true, true), (false, true), (false, true), (false, true), (true, true), (false, true), (true, true), (true, true), (true, true), (false, true)]
  | _ => [(false, true), (true, true), (false, true), (false, true), (true, true), (true, true), (true, true), (false, true), (true, true), (true, true), (true, true), (true, true)]

private def upperScalar : Fin 9 → F
  | 0 => ⟨1,0⟩
  | 1 => ⟨0,1⟩
  | 2 => ⟨2,2⟩
  | 3 => ⟨1,1⟩
  | 4 => ⟨0,2⟩
  | 5 => ⟨0,1⟩
  | 6 => ⟨0,2⟩
  | 7 => ⟨2,2⟩
  | _ => ⟨0,2⟩

private def upperUnit (i : Fin 9) : Fˣ := Units.mk0 (upperScalar i) (by
  have h : ∀ i, upperScalar i ≠ 0 := by decide +kernel
  exact h i)

private theorem upper_cert (i : Fin 9) :
    eval canonicalGenerator (upperWord i) = ⟨(1 : Z),Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (fieldElement i)))⟩ := by
  rw [←map_eval]
  apply projective_scalar _ _ _ (upperUnit i)
  · revert i
    apply allFin
    decide +kernel
  · apply Matrix.GeneralLinearGroup.ext
    intro j k
    fin_cases j <;> fin_cases k <;> revert i <;> apply allFin <;> decide +kernel

private def lowerWord : Fin 9 → Word Bool
  | 0 => []
  | 1 => [(false, true), (true, true), (false, true), (true, true), (true, true), (true, true), (false, true), (true, true), (true, true), (true, true)]
  | 2 => [(false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (true, true), (false, true), (false, true), (true, true)]
  | 3 => [(true, true), (true, true), (false, true), (true, true), (false, true), (true, true), (true, true), (true, true), (false, true), (true, true)]
  | 4 => [(true, true), (true, true), (true, true), (false, true), (true, true), (false, true), (true, true), (true, true), (true, true), (false, true)]
  | 5 => [(false, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true), (false, true), (false, true)]
  | 6 => [(true, true), (false, true), (false, true), (true, true), (false, true), (false, true), (true, true), (true, true), (true, true), (false, true), (false, true), (true, true)]
  | 7 => [(true, true), (false, true), (true, true), (false, true), (true, true), (true, true), (true, true), (false, true), (true, true), (true, true)]
  | _ => [(false, true), (true, true), (true, true), (true, true), (false, true), (false, true), (true, true), (false, true), (false, true), (true, true), (true, true), (false, true)]

private def lowerScalar : Fin 9 → F
  | 0 => ⟨1,0⟩
  | 1 => ⟨1,1⟩
  | 2 => ⟨1,1⟩
  | 3 => ⟨1,1⟩
  | 4 => ⟨1,1⟩
  | 5 => ⟨1,1⟩
  | 6 => ⟨0,1⟩
  | 7 => ⟨1,1⟩
  | _ => ⟨0,1⟩

private def lowerUnit (i : Fin 9) : Fˣ := Units.mk0 (lowerScalar i) (by
  have h : ∀ i, lowerScalar i ≠ 0 := by decide +kernel
  exact h i)

private theorem lower_cert (i : Fin 9) :
    eval canonicalGenerator (lowerWord i) = ⟨(1 : Z),Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) (fieldElement i)))⟩ := by
  rw [←map_eval]
  apply projective_scalar _ _ _ (lowerUnit i)
  · revert i
    apply allFin
    decide +kernel
  · apply Matrix.GeneralLinearGroup.ext
    intro j k
    fin_cases j <;> fin_cases k <;> revert i <;> apply allFin <;> decide +kernel

private def diagonalWord : Fin 8 → Word Bool
  | 0 => []
  | 1 => [(false, true), (false, true), (false, true), (false, true), (false, true), (true, true), (true, true), (false, true), (false, true), (false, true)]
  | 2 => [(false, true), (false, true), (false, true), (false, true), (true, true), (true, true), (true, true), (true, true), (false, true), (false, true)]
  | 3 => [(false, true), (true, true), (false, true), (false, true), (true, true), (true, true), (true, true), (true, true), (true, true)]
  | 4 => [(true, true), (true, true), (true, true), (false, true), (true, true), (false, true), (false, true), (false, true), (true, true), (false, true), (false, true)]
  | 5 => [(true, true), (false, true), (true, true), (false, true), (true, true), (true, true), (true, true), (false, true), (true, true), (true, true), (true, true), (true, true)]
  | 6 => [(false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (true, true), (false, true), (true, true), (false, true), (true, true)]
  | _ => [(false, true), (false, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (false, true)]

private def diagonalScalar : Fin 8 → F
  | 0 => ⟨1,0⟩
  | 1 => ⟨2,1⟩
  | 2 => ⟨0,1⟩
  | 3 => ⟨1,0⟩
  | 4 => ⟨0,2⟩
  | 5 => ⟨2,2⟩
  | 6 => ⟨1,0⟩
  | _ => ⟨0,2⟩

private def diagonalUnit (i : Fin 8) : Fˣ := Units.mk0 (diagonalScalar i) (by
  have h : ∀ i, diagonalScalar i ≠ 0 := by decide +kernel
  exact h i)

private theorem diagonal_cert (i : Fin 8) :
    eval canonicalGenerator (diagonalWord i) = ⟨(1 : Z),Matrix.ProjGenLinGroup.mk (diagonal (unitElement i))⟩ := by
  rw [←map_eval]
  apply projective_scalar _ _ _ (diagonalUnit i)
  · revert i
    apply allFin
    decide +kernel
  · apply Matrix.GeneralLinearGroup.ext
    intro j k
    fin_cases j <;> fin_cases k <;> revert i <;> apply allFin <;> decide +kernel

private def kernelWord : Fin 1 → Word Bool
  | _ => [(false, true), (false, true), (false, true), (true, true), (true, true), (false, true), (true, true), (true, true), (true, true), (true, true), (true, true), (false, true), (true, true), (true, true)]

private def kernelScalar : Fin 1 → F
  | _ => ⟨1,2⟩

private def kernelUnit (i : Fin 1) : Fˣ := Units.mk0 (kernelScalar i) (by
  have h : ∀ i, kernelScalar i ≠ 0 := by decide +kernel
  exact h i)

private theorem kernel_cert (i : Fin 1) :
    eval canonicalGenerator (kernelWord i) = ⟨Multiplicative.ofAdd 1,Matrix.ProjGenLinGroup.mk ((1 : GL9))⟩ := by
  rw [←map_eval]
  apply projective_scalar _ _ _ (kernelUnit i)
  · revert i
    apply allFin
    decide +kernel
  · apply Matrix.GeneralLinearGroup.ext
    intro j k
    fin_cases j <;> fin_cases k <;> revert i <;> apply allFin <;> decide +kernel

private theorem word_mem (w : Word Bool) :
    eval canonicalGenerator w ∈ closure ({canonicalFirst,canonicalSecond} : Set Canonical) := by
  have hg (b : Bool) : canonicalGenerator b ∈ closure ({canonicalFirst,canonicalSecond} : Set Canonical) := by
    cases b <;> apply Subgroup.subset_closure <;> simp [canonicalGenerator]
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons]
    apply Subgroup.mul_mem _ _ ih
    split
    · exact hg a.1
    · exact Subgroup.inv_mem _ (hg a.1)

set_option maxHeartbeats 1200000 in
/-- The exact third-local pair generates the full canonical cubic normalizer. -/
theorem canonical_generates : closure ({canonicalFirst,canonicalSecond} : Set Canonical) = ⊤ := by
  let H := closure ({canonicalFirst,canonicalSecond} : Set Canonical)
  let j : Matrix.SpecialLinearGroup (Fin 2) F →* Canonical :=
    SemidirectProduct.inr.comp (Matrix.ProjGenLinGroup.mk.comp Matrix.SpecialLinearGroup.toGL)
  have hSL (g : Matrix.SpecialLinearGroup (Fin 2) F) : j g ∈ H := by
    apply Matrix.SL2.transvection_induction (fun g => j g ∈ H) ?_ ?_ g
    · intro a b hab c
      obtain ⟨i,rfl⟩ := fieldElement_surjective c
      fin_cases a <;> fin_cases b
      · exact (hab rfl).elim
      · change ⟨1,Matrix.ProjGenLinGroup.mk _⟩ ∈ H
        rw [←upper_cert]
        exact word_mem _
      · change ⟨1,Matrix.ProjGenLinGroup.mk _⟩ ∈ H
        rw [←lower_cert]
        exact word_mem _
      · exact (hab rfl).elim
    · intro a b ha hb
      rw [map_mul]
      exact H.mul_mem ha hb
  have hdiag (d : Fˣ) : (SemidirectProduct.inr (Matrix.ProjGenLinGroup.mk (diagonal d)) : Canonical) ∈ H := by
    obtain ⟨i,rfl⟩ := unitElement_surjective d
    change ⟨1,Matrix.ProjGenLinGroup.mk _⟩ ∈ H
    rw [←diagonal_cert]
    exact word_mem _
  have hinr (p : P) : (SemidirectProduct.inr p : Canonical) ∈ H := by
    obtain ⟨g,rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective p
    let d := diagonal g.det
    let b := d⁻¹ * g
    have hdet : b.det = 1 := by simp [b,d,map_mul,diagonal_det]
    have hbdet : (b : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      exact congrArg Units.val hdet
    let s : Matrix.SpecialLinearGroup (Fin 2) F := ⟨b.val,hbdet⟩
    have hs : Matrix.SpecialLinearGroup.toGL s = b := by
      apply Matrix.GeneralLinearGroup.ext
      intro i k
      rfl
    have he : g = d * Matrix.SpecialLinearGroup.toGL s := by rw [hs]; simp [b]
    rw [he,map_mul,map_mul]
    exact H.mul_mem (hdiag g.det) (hSL s)
  have hz : (SemidirectProduct.inl (Multiplicative.ofAdd 1) : Canonical) ∈ H := by
    change (⟨Multiplicative.ofAdd 1,1⟩ : Canonical) ∈ H
    have he := kernel_cert 0
    simp only [map_one] at he
    rw [←he]
    exact word_mem _
  have hinl (a : Z) : (SemidirectProduct.inl a : Canonical) ∈ H := by
    have ha : ∀ a : Z, ∃ n : Fin 3, (Multiplicative.ofAdd (1 : ZMod 3)) ^ n.val = a := by decide +kernel
    obtain ⟨n,rfl⟩ := ha a
    rw [map_pow]
    exact H.pow_mem hz n.val
  apply top_unique
  intro g _
  rw [←SemidirectProduct.inl_left_mul_inr_right g]
  exact H.mul_mem (hinl _) (hinr _)

end Sporadic.Janko3.AmalgamPresentation.NineCoordinates
