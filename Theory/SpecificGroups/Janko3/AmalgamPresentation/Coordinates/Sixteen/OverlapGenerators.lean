module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Sixteen.Orientation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-! Explicit generation witnesses for both marked first-local overlaps. -/
@[expose] public section
set_option Elab.async false
namespace Sporadic.Janko3.AmalgamPresentation.SixteenCoordinates
open Subgroup Subgroup.CosetWordCertificate

def pointWords : Subgroup ComputableModel := closure ({pointFirst,pointSecond} : Set _)
def pairWords : Subgroup ComputableModel := closure ({pairFirst,pairSecond} : Set _)
private def pointGen (b : Bool) : ComputableModel := if b then pointSecond else pointFirst
private def pairGen (b : Bool) : ComputableModel := if b then pairSecond else pairFirst
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

private theorem fieldElement_surjective : Function.Surjective fieldElement := by
  change ∀ x : F, ∃ i : Fin 16, fieldElement i = x
  decide +kernel

def primitiveUnit : Fˣ := ⟨z,⟨⟨1,1⟩,⟨1,1⟩⟩,by decide +kernel,by decide +kernel⟩
def diagonalGenerator : ComputableModel := SemidirectProduct.inl (BenderSuzuki.Converse.tor primitiveUnit)
def fieldGenerator : ComputableModel := SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))
def swapGenerator : ComputableModel := SemidirectProduct.inl (BenderSuzuki.Converse.weyl F)

private theorem word_mem {G : Type*} [Group G] (a b : G) (w : Word Bool) :
    eval (fun i => if i then b else a) w ∈ closure ({a,b} : Set G) := by
  have hg (i : Bool) : (if i then b else a) ∈ closure ({a,b} : Set G) := by
    cases i <;> apply Subgroup.subset_closure <;> simp
  induction w with
  | nil => simp
  | cons x w ih =>
    rw [eval_cons]
    apply Subgroup.mul_mem _ _ ih
    split
    · exact hg x.1
    · exact Subgroup.inv_mem _ (hg x.1)

private def pointUpperWord : Fin 16 → Word Bool
  | 0 => []
  | 1 => [(true, true), (false, false), (true, false), (false, false)]
  | 2 => [(true, true), (false, true), (false, true), (true, false), (false, true), (false, true)]
  | 3 => [(false, true), (true, false), (false, true), (true, true)]
  | 4 => [(true, false), (true, false), (false, false), (true, true), (true, true), (false, true)]
  | 5 => [(false, true), (true, false), (true, false), (false, false), (true, true), (true, true)]
  | 6 => [(true, false), (false, true), (false, true), (true, true), (false, true), (false, true)]
  | 7 => [(true, true), (false, true), (true, false), (true, false), (false, false), (true, true)]
  | 8 => [(false, false), (true, true), (false, true), (true, false), (false, true), (false, true)]
  | 9 => [(true, false), (false, true), (true, false), (false, true), (true, true), (true, true)]
  | 10 => [(true, true), (false, true), (true, false), (false, true)]
  | 11 => [(false, false), (true, false), (false, true), (true, true), (false, true), (false, true)]
  | 12 => [(false, true), (true, true), (false, false), (true, false), (false, false), (false, false)]
  | 13 => [(true, false), (false, true), (true, true), (false, true)]
  | 14 => [(false, true), (true, false), (false, true), (false, true), (true, true), (false, true)]
  | _ => [(true, true), (true, true), (false, false), (true, false), (true, false), (false, true)]

private theorem upper_cert (k : Fin 16) : eval pointGen (pointUpperWord k) =
    SemidirectProduct.inl (BenderSuzuki.Converse.uni (fieldElement k)) := by
  apply SemidirectProduct.ext
  · apply Subtype.ext
    funext i j
    fin_cases i <;> fin_cases j <;> revert k <;> apply allFin <;> decide +kernel
  · revert k
    apply allFin
    decide +kernel

theorem upper_mem_pointWords (c : F) :
    SemidirectProduct.inl (BenderSuzuki.Converse.uni c) ∈ pointWords := by
  obtain ⟨k,rfl⟩ := fieldElement_surjective c
  rw [←upper_cert]
  exact word_mem _ _ _

private def pointDiagonalWord : Word Bool := [(false, true), (true, false), (false, false), (false, false), (true, false), (false, false)]
private theorem pointDiagonal_cert : eval pointGen pointDiagonalWord = diagonalGenerator := by
  apply SemidirectProduct.ext
  · apply Subtype.ext
    funext i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · decide +kernel
theorem pointDiagonal_mem : diagonalGenerator ∈ pointWords := by
  rw [←pointDiagonal_cert]
  exact word_mem _ _ _

private def pointFieldWord : Word Bool := [(false, true), (false, true), (true, true), (false, false), (true, true), (false, false), (true, true)]
private theorem pointField_cert : eval pointGen pointFieldWord = fieldGenerator := by
  apply SemidirectProduct.ext
  · apply Subtype.ext
    funext i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · decide +kernel
theorem pointField_mem : fieldGenerator ∈ pointWords := by
  rw [←pointField_cert]
  exact word_mem _ _ _

private def pairDiagonalWord : Word Bool := [(true, true), (false, true), (true, true), (false, false), (true, true), (false, true), (true, true), (false, true)]
private theorem pairDiagonal_cert : eval pairGen pairDiagonalWord = diagonalGenerator := by
  apply SemidirectProduct.ext
  · apply Subtype.ext
    funext i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · decide +kernel
theorem pairDiagonal_mem : diagonalGenerator ∈ pairWords := by
  rw [←pairDiagonal_cert]
  exact word_mem _ _ _

private def pairFieldWord : Word Bool := [(false, true), (true, true), (false, false), (true, true), (false, true)]
private theorem pairField_cert : eval pairGen pairFieldWord = fieldGenerator := by
  apply SemidirectProduct.ext
  · apply Subtype.ext
    funext i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · decide +kernel
theorem pairField_mem : fieldGenerator ∈ pairWords := by
  rw [←pairField_cert]
  exact word_mem _ _ _

private def pairSwapWord : Word Bool := [(true, true), (false, true), (true, true), (false, true), (true, true)]
private theorem pairSwap_cert : eval pairGen pairSwapWord = swapGenerator := by
  apply SemidirectProduct.ext
  · apply Subtype.ext
    funext i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · decide +kernel
theorem pairSwap_mem : swapGenerator ∈ pairWords := by
  rw [←pairSwap_cert]
  exact word_mem _ _ _

theorem primitiveUnit_order : orderOf primitiveUnit = 15 := by
  apply (orderOf_eq_iff (by decide : 0 < 15)).mpr
  refine ⟨by decide +kernel, ?_⟩
  intro m hm hp
  interval_cases m <;> decide +kernel

theorem primitiveUnit_generates : zpowers primitiveUnit = ⊤ := by
  apply eq_top_of_card_eq
  rw [Nat.card_zpowers,primitiveUnit_order,Nat.card_units,Nat.card_eq_fintype_card,card]

end Sporadic.Janko3.AmalgamPresentation.SixteenCoordinates
