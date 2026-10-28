module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Basic
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Action
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Irreducible
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Transport

/-!
# Recognition from explicit natural extension data

`NaturalExtension` records a surjection onto the actual matrix group SL₂, its
normal elementary abelian kernel, commutator generation of that kernel, and an
equivariant identification of its central quotient with the natural module.
It contains no short-group or perfectness assumption.

For finite characteristic-two fields with more than two elements, the exported
results prove perfectness, identify the two-core and its quotient, determine the
generalized Fitting subgroup, and prove the invariant-subgroup interval. The
ChapterC adapter assembles these results into the source block definitions.
Transport is through actual multiplicative equivalences of the local groups.

Source: Aschbacher–Smith, C.1.7/C.1.12 and F.1.12(I)(2), printed pp.123–124
and 262–264 of the combined manuscript of 1 March 2004.
-/
