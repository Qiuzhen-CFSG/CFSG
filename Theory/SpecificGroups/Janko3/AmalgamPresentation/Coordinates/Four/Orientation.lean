module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Four.ModelMarking
public import Theory.SpecificGroups.Janko3.SourceRecognition.SingerField
import Mathlib.Tactic.FinCases

/-!
# Simultaneous affine orientation of the actual second-local overlaps

Translation by (1+ω,1) sends the fixed point of the marked order-180
subgroup to zero. In this same coordinate system the marked order-480
subgroup has the existing Singer field-affine position. All four overlap
words are the original signed words; their coordinates are checked directly.
-/

@[expose] public noncomputable section
namespace Sporadic.Janko3.AmalgamPresentation.FourCoordinates
open Subgroup Subgroup.CosetWordCertificate Matrix
open Representation.SL2FourNatural hiding Plane
open Representation.CentralCubicNaturalFour

private theorem computation_ext {x y : Affine}
    (hv : ∀ i, x.left.toAdd i = y.left.toAdd i)
    (hm : ∀ i j, x.right.val i j = y.right.val i j) : x = y := by
  apply SemidirectProduct.ext
  · exact congrArg Multiplicative.ofAdd (funext hv)
  · exact Units.ext (funext fun i => funext (hm i))

def orientation : Affine :=
  ⟨Multiplicative.ofAdd ![⟨1,1⟩,1],
    ⟨!![1,0;0,1],!![1,0;0,1],by decide +kernel,by decide +kernel⟩⟩

def orientedFirst : Affine :=
  ⟨Multiplicative.ofAdd ![0,⟨0,1⟩],
    ⟨!![⟨0,1⟩,0;⟨1,1⟩,1],!![⟨1,1⟩,0;⟨0,1⟩,1],by decide +kernel,by decide +kernel⟩⟩

def orientedSecond : Affine :=
  ⟨Multiplicative.ofAdd ![⟨1,1⟩,0],
    ⟨!![⟨0,1⟩,⟨0,1⟩;0,⟨1,1⟩],!![⟨1,1⟩,⟨0,1⟩;0,⟨0,1⟩],by decide +kernel,by decide +kernel⟩⟩

theorem orientedFirst_eq : orientedFirst = orientation * first * orientation⁻¹ := by
  apply computation_ext
  · intro i; fin_cases i <;> decide +kernel
  · intro i j; fin_cases i <;> fin_cases j <;> decide +kernel

theorem orientedSecond_eq : orientedSecond = orientation * second * orientation⁻¹ := by
  apply computation_ext
  · intro i; fin_cases i <;> decide +kernel
  · intro i j; fin_cases i <;> fin_cases j <;> decide +kernel

def orientedGenerator (b : Bool) : Affine := if b then orientedSecond else orientedFirst

def singerFirst : Affine :=
  ⟨Multiplicative.ofAdd ![⟨0,1⟩,0],
    ⟨!![0,⟨1,1⟩;⟨0,1⟩,⟨0,1⟩],!![⟨0,1⟩,⟨1,1⟩;⟨0,1⟩,0],by decide +kernel,by decide +kernel⟩⟩

def singerFirstWord : Word Bool := [(true, true), (false, true), (false, true), (true, true), (false, false), (true, true), (false, true), (false, true)]
theorem singerFirst_word : eval orientedGenerator singerFirstWord = singerFirst := by
  apply computation_ext
  · intro i; fin_cases i <;> decide +kernel
  · intro i j; fin_cases i <;> fin_cases j <;> decide +kernel

def singerSecond : Affine :=
  ⟨Multiplicative.ofAdd ![1,1],
    ⟨!![⟨0,1⟩,0;1,⟨0,1⟩],!![⟨1,1⟩,0;⟨0,1⟩,⟨1,1⟩],by decide +kernel,by decide +kernel⟩⟩

def singerSecondWord : Word Bool := [(false, true), (false, true), (true, true), (true, true), (false, true), (true, true), (false, false), (true, true), (false, true), (false, true), (false, true)]
theorem singerSecond_word : eval orientedGenerator singerSecondWord = singerSecond := by
  apply computation_ext
  · intro i; fin_cases i <;> decide +kernel
  · intro i j; fin_cases i <;> fin_cases j <;> decide +kernel

def linearFirst : Affine :=
  ⟨Multiplicative.ofAdd ![0,0],
    ⟨!![1,0;⟨0,1⟩,1],!![1,0;⟨0,1⟩,1],by decide +kernel,by decide +kernel⟩⟩

def linearFirstWord : Word Bool := [(false, true), (false, true), (true, false), (false, false), (true, false), (false, false), (true, false), (false, false), (true, false), (true, false), (false, false), (false, false)]
theorem linearFirst_word : eval orientedGenerator linearFirstWord = linearFirst := by
  apply computation_ext
  · intro i; fin_cases i <;> decide +kernel
  · intro i j; fin_cases i <;> fin_cases j <;> decide +kernel

def linearSecond : Affine :=
  ⟨Multiplicative.ofAdd ![0,0],
    ⟨!![⟨0,1⟩,⟨1,1⟩;⟨1,1⟩,0],!![0,⟨0,1⟩;⟨0,1⟩,1],by decide +kernel,by decide +kernel⟩⟩

def linearSecondWord : Word Bool := [(false, true), (true, false), (false, false), (false, false), (true, true), (false, false), (true, false), (true, false), (false, false), (false, false), (true, false), (false, false)]
theorem linearSecond_word : eval orientedGenerator linearSecondWord = linearSecond := by
  apply computation_ext
  · intro i; fin_cases i <;> decide +kernel
  · intro i j; fin_cases i <;> fin_cases j <;> decide +kernel

def singerWords : Subgroup Affine := closure ({singerFirst,singerSecond} : Set Affine)
def linearWords : Subgroup Affine := closure ({linearFirst,linearSecond} : Set Affine)

end Sporadic.Janko3.AmalgamPresentation.FourCoordinates
