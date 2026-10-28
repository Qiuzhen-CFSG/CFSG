module

public import Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimary.PresentationFaithfulness.PositiveCollection
public import Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimary.PresentationFaithfulness

/-!
# Applying degree-four positive-root and Bruhat collection

The proved collection statements discharge both upper-subgroup inputs in
`matrixMap_injective_of_bruhat`. Only collection of a Weyl-kernel element
into the literal torus subgroup remains explicit; its proof belongs to the
independent Weyl-kernel branch.

Source: Steinberg, *Lectures on Chevalley Groups*, §6, Theorem 8(b),
printed p.71 (`refs/KGroup/GLS3/Chapter2St1.tex`).
-/

@[expose] public section

namespace Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimaryFaithfulness

open Theory.SpecificGroups.LinearHigher
variable {F : Type*} [Field F] [Finite F]

/-- Positive and Bruhat collection leave precisely the Weyl-kernel input. -/
theorem matrixMap_injective_of_weylKernelInTorus (hW : WeylKernelInTorus F) :
    Function.Injective (matrixMap (n := 4) (F := F)) :=
  matrixMap_injective_of_bruhat bruhatCover upperFaithful hW

end Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimaryFaithfulness
