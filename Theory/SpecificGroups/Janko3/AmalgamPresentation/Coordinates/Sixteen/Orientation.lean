module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Sixteen.ModelMarking
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.Point
import Mathlib.Tactic.FinCases

/-!
# Concrete orientation of the first local pair and its overlap words

A determinant-one coordinate change sends the fixed point of the order-480
word subgroup to infinity and the second endpoint of the order-60 word
subgroup to zero. The four overlap elements are the literal original words,
with small matrix certificates and explicit root/torus/field-actor words.
The cardinal and full-overlap identifications are proved separately.
-/

@[expose] public section
set_option Elab.async false
namespace Sporadic.Janko3.AmalgamPresentation.SixteenCoordinates
open Subgroup Subgroup.CosetWordCertificate

def orientation : ComputableModel := ⟨⟨!![⟨⟨0,1⟩,⟨0,0⟩⟩, ⟨⟨1,1⟩,⟨1,1⟩⟩; ⟨⟨0,1⟩,⟨0,0⟩⟩, ⟨⟨0,0⟩,⟨1,1⟩⟩], by decide +kernel⟩, 1⟩
def orientedFirst : ComputableModel := ⟨⟨!![⟨⟨0,1⟩,⟨0,1⟩⟩, ⟨⟨0,0⟩,⟨0,0⟩⟩; ⟨⟨1,0⟩,⟨0,0⟩⟩, ⟨⟨0,0⟩,⟨0,1⟩⟩], by decide +kernel⟩, 1⟩
def orientedSecond : ComputableModel := ⟨⟨!![⟨⟨1,1⟩,⟨0,1⟩⟩, ⟨⟨1,0⟩,⟨0,1⟩⟩; ⟨⟨0,1⟩,⟨0,0⟩⟩, ⟨⟨1,1⟩,⟨0,1⟩⟩], by decide +kernel⟩, Multiplicative.ofAdd 1⟩

private theorem computation_ext {x y : ComputableModel}
    (hm : ∀ i j, x.left.val i j = y.left.val i j) (hr : x.right = y.right) : x = y := by
  apply SemidirectProduct.ext
  · exact Subtype.ext (funext (fun i => funext (hm i)))
  · exact hr

theorem orientedFirst_eq : orientedFirst = orientation * first * orientation⁻¹ := by
  apply computation_ext
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · decide +kernel

theorem orientedSecond_eq : orientedSecond = orientation * second * orientation⁻¹ := by
  apply computation_ext
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · decide +kernel

def orientedGenerator (b : Bool) : ComputableModel := if b then orientedSecond else orientedFirst

def pointFirst : ComputableModel := ⟨⟨!![⟨⟨0,1⟩,⟨1,1⟩⟩, ⟨⟨0,1⟩,⟨0,0⟩⟩; ⟨⟨0,0⟩,⟨0,0⟩⟩, ⟨⟨1,0⟩,⟨1,1⟩⟩], by decide +kernel⟩, 1⟩
def pointFirstWord : Word Bool := [(true, false), (false, false), (true, false)]
theorem pointFirst_word : eval orientedGenerator pointFirstWord = pointFirst := by
  apply computation_ext
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · decide +kernel

def pointSecond : ComputableModel := ⟨⟨!![⟨⟨1,0⟩,⟨1,0⟩⟩, ⟨⟨0,1⟩,⟨1,1⟩⟩; ⟨⟨0,0⟩,⟨0,0⟩⟩, ⟨⟨0,0⟩,⟨1,1⟩⟩], by decide +kernel⟩, Multiplicative.ofAdd 1⟩
def pointSecondWord : Word Bool := [(true, true), (false, true), (true, true), (false, true), (false, true), (true, false), (false, true), (true, true), (true, true), (true, true), (false, false), (true, false)]
theorem pointSecond_word : eval orientedGenerator pointSecondWord = pointSecond := by
  apply computation_ext
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · decide +kernel

def pairFirst : ComputableModel := ⟨⟨!![⟨⟨1,0⟩,⟨0,1⟩⟩, ⟨⟨0,0⟩,⟨0,0⟩⟩; ⟨⟨0,0⟩,⟨0,0⟩⟩, ⟨⟨0,1⟩,⟨1,0⟩⟩], by decide +kernel⟩, Multiplicative.ofAdd 1⟩
def pairFirstWord : Word Bool := [(true, true), (false, true), (true, true), (true, true), (false, true), (false, true), (true, true), (false, true), (true, false), (false, false), (false, false)]
theorem pairFirst_word : eval orientedGenerator pairFirstWord = pairFirst := by
  apply computation_ext
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · decide +kernel

def pairSecond : ComputableModel := ⟨⟨!![⟨⟨0,0⟩,⟨0,0⟩⟩, ⟨⟨1,0⟩,⟨1,1⟩⟩; ⟨⟨0,1⟩,⟨1,1⟩⟩, ⟨⟨0,0⟩,⟨0,0⟩⟩], by decide +kernel⟩, 1⟩
def pairSecondWord : Word Bool := [(false, true), (true, true), (false, true), (true, false), (true, false), (false, false), (true, false), (true, false), (false, false), (true, false), (false, false)]
theorem pairSecond_word : eval orientedGenerator pairSecondWord = pairSecond := by
  apply computation_ext
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · decide +kernel

end Sporadic.Janko3.AmalgamPresentation.SixteenCoordinates
