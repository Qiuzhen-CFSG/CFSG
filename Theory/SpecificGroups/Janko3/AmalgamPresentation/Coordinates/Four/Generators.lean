module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Four.Basic
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Four.Presentation.Basic
import Mathlib.Tactic.FinCases

/-!
# The actual affine pair generates AGL₂(4)

Short signed words recover each of the sixteen translations, all upper and
lower root matrices, and each scalar matrix. Matrix transvection induction
and the scalar-times-special-linear decomposition then prove generation.
The exact five second-local relators are checked on the literal affine
coordinates. Every finite identity is reduced by Lean's kernel.
Word discovery is retained in `Scratch/J3ModelCoordinates/Four/native_words.py`.
-/

@[expose] public noncomputable section
set_option Elab.async false
namespace Sporadic.Janko3.AmalgamPresentation.FourCoordinates
open Subgroup Subgroup.CosetWordCertificate Matrix
open Representation.SL2FourNatural hiding Plane
open Representation.CentralCubicNaturalFour

private def fieldElement : Fin 4 → F
  | 0 => 0
  | 1 => 1
  | 2 => ⟨0,1⟩
  | _ => ⟨1,1⟩
private theorem fieldElement_surjective : Function.Surjective fieldElement := by decide +kernel

private def generator : Bool → Affine := fun b => if b then second else first

private def translationsWord : Fin 16 → Word Bool
  | 0 => []
  | 1 => [(false, true), (true, false), (false, false), (true, false), (false, true), (true, false), (false, true), (false, true), (true, false)]
  | 2 => [(false, true), (false, true), (false, true)]
  | 3 => [(true, true), (false, true), (true, false), (false, true), (false, true), (false, true), (true, true), (false, false), (true, false)]
  | 4 => [(false, true), (true, true), (false, true), (true, true), (false, false), (true, true), (false, true), (true, true), (false, true)]
  | 5 => [(false, true), (true, false), (false, true), (false, true), (false, true), (true, true), (false, false)]
  | 6 => [(false, false), (true, true), (false, true), (true, true), (false, false), (true, true), (false, false), (false, false), (true, true)]
  | 7 => [(false, true), (true, true), (false, true), (false, true), (false, true), (true, false), (false, false)]
  | 8 => [(false, false), (true, true), (false, true), (false, true), (false, true), (true, false), (false, true)]
  | 9 => [(false, false), (true, true), (false, true), (true, true), (false, false), (true, true), (false, true), (true, true)]
  | 10 => [(false, false), (true, false), (false, true), (false, true), (false, true), (true, true), (false, true)]
  | 11 => [(false, true), (false, true), (true, true), (false, true), (true, true), (false, false), (true, true), (false, true), (true, true)]
  | 12 => [(false, true), (true, false), (false, false), (true, false), (false, true), (true, false), (false, false), (true, false)]
  | 13 => [(true, true), (false, true), (false, true), (false, true), (true, false)]
  | 14 => [(false, true), (true, true), (false, false), (true, true), (false, false), (false, false), (true, true), (false, false), (true, true)]
  | _ => [(true, false), (false, true), (false, true), (false, true), (true, true)]

private def upperWord : Fin 4 → Word Bool
  | 0 => []
  | 1 => [(false, true), (true, true), (false, false), (true, false), (false, false), (false, false), (true, true), (false, false)]
  | 2 => [(false, true), (false, true), (false, true), (true, true), (false, true), (true, true), (false, false)]
  | _ => [(false, true), (true, true), (false, true), (false, true), (true, true)]

private def lowerWord : Fin 4 → Word Bool
  | 0 => []
  | 1 => [(true, false), (false, true), (false, true), (true, false), (false, false), (true, false), (false, true), (false, true), (true, true)]
  | 2 => [(false, true), (true, true), (false, false), (true, true), (false, true), (false, true), (true, false), (false, true), (true, true)]
  | _ => [(false, true), (true, false), (false, true), (true, true), (false, false), (true, false), (false, false), (true, false)]

private def scalarWord : Fin 3 → Word Bool
  | 0 => []
  | 1 => [(true, false), (false, false), (true, false), (false, false), (true, true), (false, false), (true, false), (false, false), (true, false)]
  | _ => [(true, true), (false, true), (true, true), (false, true), (true, false), (false, true), (true, true), (false, true), (true, true)]

private def vectorElement (i : Fin 16) : Plane :=
  Multiplicative.ofAdd ![fieldElement ⟨i.val / 4,by omega⟩,
    fieldElement ⟨i.val % 4,Nat.mod_lt _ (by decide)⟩]

private theorem vectorElement_surjective : Function.Surjective vectorElement := by decide +kernel

private theorem translations_cert (i : Fin 16) :
    eval generator (translationsWord i) = SemidirectProduct.inl (vectorElement i) := by
  apply SemidirectProduct.ext
  · apply congrArg Multiplicative.ofAdd
    funext j
    fin_cases j <;> revert i <;> decide +kernel
  · apply Units.ext
    funext j k
    fin_cases j <;> fin_cases k <;> revert i <;> decide +kernel

private theorem upper_cert (i : Fin 4) : eval generator (upperWord i) =
    SemidirectProduct.inr (SpecialLinearGroup.toGL
      (SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (fieldElement i))) := by
  apply SemidirectProduct.ext
  · apply congrArg Multiplicative.ofAdd
    funext j
    fin_cases j <;> revert i <;> decide +kernel
  · apply Units.ext
    funext j k
    fin_cases j <;> fin_cases k <;> revert i <;> decide +kernel

private theorem lower_cert (i : Fin 4) : eval generator (lowerWord i) =
    SemidirectProduct.inr (SpecialLinearGroup.toGL
      (SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) (fieldElement i))) := by
  apply SemidirectProduct.ext
  · apply congrArg Multiplicative.ofAdd
    funext j
    fin_cases j <;> revert i <;> decide +kernel
  · apply Units.ext
    funext j k
    fin_cases j <;> fin_cases k <;> revert i <;> decide +kernel

private def scalarElement (i : Fin 3) : Fˣ :=
  match i with
  | 0 => 1
  | 1 => ⟨⟨0,1⟩,⟨1,1⟩,by decide +kernel,by decide +kernel⟩
  | _ => ⟨⟨1,1⟩,⟨0,1⟩,by decide +kernel,by decide +kernel⟩
private theorem scalarElement_surjective : Function.Surjective scalarElement := by decide +kernel

private theorem scalar_cert (i : Fin 3) : eval generator (scalarWord i) =
    SemidirectProduct.inr (GeneralLinearGroup.scalar (Fin 2) (scalarElement i)) := by
  apply SemidirectProduct.ext
  · apply congrArg Multiplicative.ofAdd
    funext j
    fin_cases j <;> revert i <;> decide +kernel
  · apply Units.ext
    funext j k
    fin_cases j <;> fin_cases k <;> revert i <;> decide +kernel

/-- The literal affine pair satisfies exactly the original second local block. -/
theorem pair_satisfies : Presentation.Satisfies first second := by
  intro i
  fin_cases i <;> apply SemidirectProduct.ext
  all_goals first
    | (apply congrArg Multiplicative.ofAdd; funext j; fin_cases j <;> decide +kernel)
    | (apply Units.ext; funext j k; fin_cases j <;> fin_cases k <;> decide +kernel)

private theorem word_mem (w : Word Bool) :
    eval generator w ∈ closure ({first,second} : Set Affine) := by
  have hg (b : Bool) : generator b ∈ closure ({first,second} : Set Affine) := by
    cases b <;> apply Subgroup.subset_closure <;> simp [generator]
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons]
    apply Subgroup.mul_mem _ _ ih
    split
    · exact hg a.1
    · exact Subgroup.inv_mem _ (hg a.1)

/-- The exact saved pair generates the complete natural affine group. -/
theorem pair_generates : closure ({first,second} : Set Affine) = ⊤ := by
  let H := closure ({first,second} : Set Affine)
  have ht (v : Plane) : (SemidirectProduct.inl v : Affine) ∈ H := by
    obtain ⟨i,rfl⟩ := vectorElement_surjective v
    rw [←translations_cert]
    exact word_mem _
  have hs (g : SL) : (SemidirectProduct.inr (SpecialLinearGroup.toGL g) : Affine) ∈ H := by
    refine SL2.transvection_induction
      (fun g => (SemidirectProduct.inr (SpecialLinearGroup.toGL g) : Affine) ∈ H) ?_ ?_ g
    · intro i j hij c
      obtain ⟨k,rfl⟩ := fieldElement_surjective c
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · rw [←upper_cert]; exact word_mem _
      · rw [←lower_cert]; exact word_mem _
      · exact (hij rfl).elim
    · intro a b ha hb
      rw [map_mul,map_mul]
      exact H.mul_mem ha hb
  have hc (u : Fˣ) : (SemidirectProduct.inr (GeneralLinearGroup.scalar (Fin 2) u) : Affine) ∈ H := by
    obtain ⟨i,rfl⟩ := scalarElement_surjective u
    rw [←scalar_cert]
    exact word_mem _
  apply top_unique
  intro x _
  obtain ⟨⟨u,g⟩,he⟩ := SemilinearNormalizer.scalarSpecialEquiv.surjective x.right
  rw [SemilinearNormalizer.scalarSpecialEquiv_apply] at he
  have hx : x = SemidirectProduct.inl x.left * SemidirectProduct.inr x.right :=
    (SemidirectProduct.inl_left_mul_inr_right x).symm
  rw [hx,←he,map_mul]
  exact H.mul_mem (ht _) (H.mul_mem (hc _) (hs _))

end Sporadic.Janko3.AmalgamPresentation.FourCoordinates
