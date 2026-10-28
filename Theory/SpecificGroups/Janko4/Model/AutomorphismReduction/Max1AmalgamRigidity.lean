module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1AmalgamRigidity.KernelCorrection
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1AmalgamRigidity.CentralizerCorrection

/-!
# Innerness from the actual max1-centralizer amalgam

Let M be the literal ATLAS max1 subgroup of the Janko matrix model and C
the full ambient centralizer of its marked kernel pair v. If C and M
generate the model, every abstract automorphism is conjugation by an
actual element of the model.

The kernel correction aligns ambient Sylows, preserves the characteristic
kernel and its normalizer M, and corrects the actual Mathieu quotient.
The centralizer correction realizes the action on its intrinsic two-core
and leaves displacement in the marked line. The assembly uses relative
rigidity on M and the odd index of the genuine overlap in C to kill that
displacement, then generation identifies the global automorphism.

Both local correction premises are discharged here. Generation is the
sole remaining premise, to be supplied by the consuming generation proof.
No simplicity or perfectness assumption is needed.

Source context: GLS3, Table 5.3i, printed p.270, records Out(J₄) = 1
and the relevant local subgroups. This module supplies the conditional
amalgam step for that conclusion on the literal ATLAS matrix model.
-/

public section

namespace Janko4.Max1AmalgamRigidity

/-- Actual generation by the marked centralizer and max1 forces every
abstract automorphism of the matrix model to be inner. -/
theorem conj_surjective (hgen : C ⊔ M = ⊤) :
    Function.Surjective (MulAut.conj : Model →* MulAut Model) :=
  conj_surjective_of_local_corrections kernel_correction centralizer_correction hgen

/-- The conjugator belongs to the model itself. -/
theorem exists_eq_conj (hgen : C ⊔ M = ⊤) (alpha : MulAut Model) :
    ∃ g : Model, alpha = MulAut.conj g := by
  obtain ⟨g, hg⟩ := conj_surjective hgen alpha
  exact ⟨g, hg.symm⟩

end Janko4.Max1AmalgamRigidity
