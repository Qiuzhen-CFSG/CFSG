module
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.ExtensionRigidity.Injectivity.RealizationInputs
/-!
# The two marked root-center cosets

The representatives are (0,0) and (1,2). The center is enumerated by second
coordinates 0,7,14,16,23 in the polynomial field, encoded as a+5b.
Two commutation tests force the first coordinate of a central root to vanish;
the five displayed roots then exhaust the actual center. Only slot (0,0)
has zero second coordinate and is omitted in the Bruhat formula.

Source: Huppert II.10.12 and the coefficient provenance in ../source/README.md.
-/

@[expose] public section
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open HermitianForm.OddPrimeSylow.NormalizedOuter
open HermitianForm.InvolutionConjugateBounds.Five.Embedding
open Matrix
namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity.Injectivity.TableRealization
open Degrees.TrivialCalculation.MiddleFactors.Realization
abbrev form := FormTransport.standardForm tableForm
abbrev Root := hermitianUnipotentCoord form

def point : Fin 2 → Root := ![1, ⟨(1,2), by decide +kernel⟩]
def centerRaw (i : Fin 5) : Root :=
  ⟨(0, ![(0 : F25),⟨2,1⟩,⟨4,2⟩,⟨1,3⟩,⟨3,4⟩] i), by
    revert i; decide +kernel⟩

theorem centerRaw_mem (i : Fin 5) : centerRaw i ∈ Subgroup.center Root := by
  apply Subgroup.mem_center_iff.mpr
  intro z
  apply Subtype.ext
  apply Prod.ext
  · change z.val.1 + 0 = 0 + z.val.1
    simp
  · change z.val.2 + (centerRaw i).val.2 - z.val.1 * form.conj 0 =
      (centerRaw i).val.2 + z.val.2 - 0 * form.conj z.val.1
    simp [add_comm]

def centerPoint (i : Fin 5) : Subgroup.center Root := ⟨centerRaw i, centerRaw_mem i⟩
def secondWitness : Root := ⟨(⟨4,2⟩,⟨0,3⟩), by decide +kernel⟩
private theorem central_test : ∀ z : Root,
    point 1 * z = z * point 1 → secondWitness * z = z * secondWitness → z.val.1 = 0 := by
  decide +kernel
private theorem center_cover : ∀ z : Root, z.val.1 = 0 → ∃ i : Fin 5, centerRaw i = z := by
  decide +kernel

theorem centerPoint_bijective : Function.Bijective centerPoint := by
  constructor
  · have h : Function.Injective centerRaw := by decide +kernel
    intro i j hij
    exact h (congrArg Subtype.val hij)
  · intro z
    have hzero := central_test z.val
      (Subgroup.mem_center_iff.mp z.property (point 1))
      (Subgroup.mem_center_iff.mp z.property secondWitness)
    obtain ⟨i, hi⟩ := center_cover z.val hzero
    exact ⟨i, Subtype.ext hi⟩
noncomputable def centerEquiv : Subgroup.center Root ≃ Fin 5 :=
  (Equiv.ofBijective centerPoint centerPoint_bijective).symm
@[simp] theorem centerEquiv_centerPoint (i : Fin 5) : centerEquiv (centerPoint i) = i :=
  (Equiv.ofBijective centerPoint centerPoint_bijective).symm_apply_apply i

def marked (s : Fin 2) (c : Fin 5) : Root := point s * centerRaw c

theorem marked_second_zero : ∀ s c, (marked s c).val.2 = 0 ↔ s = 0 ∧ c = 0 := by
  decide +kernel
end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity.Injectivity.TableRealization
