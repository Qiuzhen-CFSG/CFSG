module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Sixteen.Basic
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.LocalBound
import Mathlib.Tactic.FinCases

/-!
# Exact first-local generator marking in canonical sixteen-field coordinates

The six frozen local relations hold entrywise. Explicit words of length at
most ten produce every upper and lower root element; an eleven-letter word
produces the pure field involution. Transvection induction then proves
generation of the actual semilinear group, and coefficient transport gives
the corresponding pair in the canonical PSL₂(16):2 model.
The untrusted word search is retained under `Scratch/J3ModelCoordinates/`.
-/

@[expose] public section
set_option Elab.async false
namespace Sporadic.Janko3.AmalgamPresentation.SixteenCoordinates
open Subgroup Subgroup.CosetWordCertificate

private def checkFin {n : Nat} (f : Fin n → Bool) : Bool :=
  (List.range n).all (fun i => if h : i < n then f ⟨i,h⟩ else true)
private theorem allFin {n : Nat} (P : Fin n → Prop) [DecidablePred P]
    (h : checkFin (fun i => decide (P i)) = true) : ∀ i, P i := by
  intro i
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simpa only [dif_pos i.isLt, decide_eq_true_eq] using hi

private def fieldElement : Fin 16 → F
  | 0 => ⟨⟨0,0⟩,⟨0,0⟩⟩
  | 1 => ⟨⟨1,0⟩,⟨0,0⟩⟩
  | 2 => ⟨⟨0,0⟩,⟨1,0⟩⟩
  | 3 => ⟨⟨1,0⟩,⟨1,0⟩⟩
  | 4 => ⟨⟨0,1⟩,⟨1,0⟩⟩
  | 5 => ⟨⟨1,1⟩,⟨1,0⟩⟩
  | 6 => ⟨⟨0,1⟩,⟨0,0⟩⟩
  | 7 => ⟨⟨1,1⟩,⟨0,0⟩⟩
  | 8 => ⟨⟨0,1⟩,⟨1,1⟩⟩
  | 9 => ⟨⟨1,1⟩,⟨1,1⟩⟩
  | 10 => ⟨⟨0,1⟩,⟨0,1⟩⟩
  | 11 => ⟨⟨1,1⟩,⟨0,1⟩⟩
  | 12 => ⟨⟨0,0⟩,⟨0,1⟩⟩
  | 13 => ⟨⟨1,0⟩,⟨0,1⟩⟩
  | 14 => ⟨⟨0,0⟩,⟨1,1⟩⟩
  | _ => ⟨⟨1,0⟩,⟨1,1⟩⟩

private lemma fieldElement_surjective : Function.Surjective fieldElement := by
  change ∀ x : F, ∃ i : Fin 16, fieldElement i = x
  decide +kernel

private def generator : Bool → ComputableModel := fun b => if b then second else first

private def upperWord : Fin 16 → Word Bool
  | 0 => []
  | 1 => [(true, true), (true, true), (false, true), (true, true), (false, true), (false, true), (true, true), (false, true), (true, true), (true, true)]
  | 2 => [(true, false), (false, true), (true, true), (false, true), (true, false), (true, false), (false, true), (true, true), (true, true)]
  | 3 => [(true, true), (false, false), (true, true), (true, true), (true, true), (false, true), (false, true), (true, true), (true, true)]
  | 4 => [(true, true), (false, false), (true, false), (false, false), (true, true), (false, true), (true, false), (false, true), (true, true), (true, true)]
  | 5 => [(true, true), (true, true), (true, true), (false, false), (true, false), (false, true), (true, true), (false, true), (false, true), (true, true)]
  | 6 => [(false, true), (true, false), (false, false), (true, false), (true, false), (false, false), (true, false), (false, true)]
  | 7 => [(false, true), (false, true), (true, false), (false, false), (true, false), (false, true), (false, true)]
  | 8 => [(false, true), (true, true), (true, true), (false, false), (true, false), (false, true), (false, true), (true, true), (true, true), (true, true)]
  | 9 => [(true, true), (false, true), (true, false), (false, true), (true, true), (false, false), (false, false), (true, true)]
  | 10 => [(false, true), (true, false), (false, true), (false, true), (true, true), (false, true), (true, false), (true, false), (false, true)]
  | 11 => [(true, true), (true, true), (false, true), (true, true), (false, false), (true, false), (false, true), (true, true), (true, true)]
  | 12 => [(false, true), (true, false), (true, false), (false, true), (true, true), (false, true), (false, true), (true, false), (false, true)]
  | 13 => [(true, true), (true, true), (false, true), (true, false), (false, false), (true, true), (false, true), (true, true), (true, true)]
  | 14 => [(true, true), (false, false), (false, false), (true, true), (false, true), (true, false), (false, true), (true, true)]
  | _ => [(true, true), (true, true), (true, true), (false, true), (false, true), (true, false), (false, false), (true, true), (true, true), (false, true)]

private theorem upper_cert (i : Fin 16) : eval generator (upperWord i) =
    SemidirectProduct.inl (Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 2) ≠ 1 by decide) (fieldElement i)) := by
  apply SemidirectProduct.ext
  · apply Subtype.ext
    funext j k
    fin_cases j <;> fin_cases k <;> revert i <;> apply allFin <;> decide +kernel
  · revert i
    apply allFin
    decide +kernel

private def lowerWord : Fin 16 → Word Bool
  | 0 => []
  | 1 => [(false, false), (true, true), (false, true), (true, false), (true, false), (false, false), (true, true), (false, true)]
  | 2 => [(false, false), (true, true), (false, true), (true, false), (true, false), (false, true), (true, false), (false, true)]
  | 3 => [(false, false), (true, true), (false, false), (false, false), (true, true), (false, true)]
  | 4 => [(false, false), (true, true), (false, true), (true, true), (true, true), (true, true), (false, true)]
  | 5 => [(false, true), (true, true), (true, true), (false, true), (true, true), (false, true), (true, false), (false, false)]
  | 6 => [(false, false), (true, true), (false, false), (true, true), (true, true), (true, true), (true, true), (true, true), (false, true)]
  | 7 => [(false, false), (true, false), (true, false), (true, false), (false, true), (false, true), (true, true), (false, true)]
  | 8 => [(false, false), (true, true), (false, false), (true, false), (true, false), (false, true), (true, true), (false, true)]
  | 9 => [(true, true), (true, true), (true, true), (false, false), (true, true), (true, true), (true, true), (false, true), (false, true)]
  | 10 => [(false, false), (true, false), (true, false), (true, false), (false, false), (true, true), (true, true), (false, true), (true, true), (false, true)]
  | 11 => [(false, false), (true, false), (false, true), (true, false), (true, false), (false, true), (true, true), (false, true)]
  | 12 => [(true, true), (false, true), (false, true), (true, false), (false, true), (true, false), (false, true), (true, false)]
  | 13 => [(false, false), (true, true), (true, true), (true, true), (false, false), (false, false), (true, false), (false, true)]
  | 14 => [(false, false), (true, true), (true, true), (true, true), (false, true), (true, true), (false, true)]
  | _ => [(false, false), (true, true), (false, false), (true, false), (true, false), (false, false), (true, true), (true, true), (true, true), (false, true)]

private theorem lower_cert (i : Fin 16) : eval generator (lowerWord i) =
    SemidirectProduct.inl (Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 2) ≠ 0 by decide) (fieldElement i)) := by
  apply SemidirectProduct.ext
  · apply Subtype.ext
    funext j k
    fin_cases j <;> fin_cases k <;> revert i <;> apply allFin <;> decide +kernel
  · revert i
    apply allFin
    decide +kernel

private def outerWord : Word Bool := [(true, false), (false, true), (true, false), (false, true), (true, false), (false, true), (true, true), (false, true), (false, true), (true, true), (false, true)]
private theorem outer_cert : eval generator outerWord =
    SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)) := by
  apply SemidirectProduct.ext
  · apply Subtype.ext
    funext i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · decide +kernel

/-- The exact six relations defining the first frozen local pair. -/
theorem pair_satisfies : LocalBound.Satisfies first second := by
  intro k
  fin_cases k <;> apply SemidirectProduct.ext
  all_goals
    first
    | (apply Subtype.ext; funext i j; fin_cases i <;> fin_cases j <;> decide +kernel)
    | decide +kernel

private theorem word_mem (w : Word Bool) :
    eval generator w ∈ closure ({first, second} : Set ComputableModel) := by
  have hg (b : Bool) : generator b ∈ closure ({first,second} : Set ComputableModel) := by
    cases b <;> apply subset_closure <;> simp [generator]
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons]
    apply Subgroup.mul_mem _ _ ih
    split
    · exact hg a.1
    · exact Subgroup.inv_mem _ (hg a.1)

/-- Actual transvection generation, using the literal root-word witnesses. -/
theorem pair_generates : closure ({first, second} : Set ComputableModel) = ⊤ := by
  let H := closure ({first,second} : Set ComputableModel)
  have hinl (g : SL) : SemidirectProduct.inl g ∈ H := by
    apply Matrix.SL2.transvection_induction (fun g => SemidirectProduct.inl g ∈ H) ?_ ?_ g
    · intro i j hij c
      obtain ⟨k,rfl⟩ := fieldElement_surjective c
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · rw [←upper_cert]
        exact word_mem _
      · rw [←lower_cert]
        exact word_mem _
      · exact (hij rfl).elim
    · intro a b ha hb
      rw [map_mul]
      exact H.mul_mem ha hb
  have hinr (a : Two) : SemidirectProduct.inr a ∈ H := by
    have hc : ∀ a : Two, a = 1 ∨ a = Multiplicative.ofAdd 1 := by decide +kernel
    rcases hc a with rfl | rfl
    · rw [map_one]
      exact H.one_mem
    · rw [←outer_cert]
      exact word_mem _
  apply top_unique
  intro g _
  rw [←SemidirectProduct.inl_left_mul_inr_right g]
  exact H.mul_mem (hinl _) (hinr _)

/-- The first marked generator in the canonical sixteen-field extension. -/
noncomputable def canonicalFirst : Theory.PSL2.BinaryFourFieldExtension.Model := modelEquiv first
/-- The second marked generator in the canonical sixteen-field extension. -/
noncomputable def canonicalSecond : Theory.PSL2.BinaryFourFieldExtension.Model := modelEquiv second

theorem canonical_satisfies : LocalBound.Satisfies canonicalFirst canonicalSecond := by
  intro i
  have he := congrArg modelEquiv (pair_satisfies i)
  change modelEquiv.toMonoidHom (LocalBound.relator first second i) =
    modelEquiv.toMonoidHom 1 at he
  rw [LocalBound.map_relator, map_one] at he
  exact he

theorem canonical_generates : closure ({canonicalFirst,canonicalSecond} :
    Set Theory.PSL2.BinaryFourFieldExtension.Model) = ⊤ := by
  have he := congrArg (Subgroup.map modelEquiv.toMonoidHom) pair_generates
  rw [map_top_of_surjective modelEquiv.toMonoidHom modelEquiv.surjective] at he
  rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton] at he
  exact he

end Sporadic.Janko3.AmalgamPresentation.SixteenCoordinates
