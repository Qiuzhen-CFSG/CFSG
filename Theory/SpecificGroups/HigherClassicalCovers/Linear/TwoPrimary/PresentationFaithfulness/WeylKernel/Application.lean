module

public import Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimary.PresentationFaithfulness.WeylKernel
public import Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimary.PresentationFaithfulness

/-!
# Applying degree-four Weyl kernel collection

The literal Weyl kernel now lies in the torus. Substituting this result into
Bruhat kernel reduction leaves precisely Bruhat coverage and faithfulness of
the positive subgroup as inputs. This application uses the original matrix
map from the Steinberg presentation, including the scalar center of SL₄.

Source: Steinberg, *Lectures on Chevalley Groups*, §6, Theorem 8(b),
printed pp.71–72 (`refs/KGroup/GLS3/Chapter2St1.tex`).
-/

public section

namespace Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimaryFaithfulness

open Theory.SpecificGroups.LinearHigher
variable {F : Type*} [Field F] [Finite F]

/-- Weyl collection discharges the Weyl premise in the literal Bruhat kernel argument. -/
theorem matrixMap_injective_of_bruhatCover
    (hcover : BruhatCover F) (hU : UpperFaithful F) :
    Function.Injective (matrixMap (n := 4) (F := F)) :=
  matrixMap_injective_of_bruhat hcover hU weylKernelInTorus

end Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimaryFaithfulness
