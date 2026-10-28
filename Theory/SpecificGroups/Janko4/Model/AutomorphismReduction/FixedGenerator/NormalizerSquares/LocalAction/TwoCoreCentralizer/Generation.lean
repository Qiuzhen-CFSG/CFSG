module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Max2Bridge
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.Conjugacy
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.Homology
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.ImageBound

/-!
# Generation of the literal involution centralizer

Conjugation by the certified bridge identifies the original ATLAS max2
subgroup with `localSubgroup`. On the other hand, the canonical action of
the whole literal centralizer on ker(a - 1) / im(a - 1) counts the
centralizer as the product of its kernel and image orders.

A lower bound 21799895040 for the word subgroup, a kernel upper bound
8192, and an image upper bound 2661120 therefore prove full generation.
The three certificate modules establish these bounds for the actual
subgroups and action. The final theorem discharges all three premises of
the retained conditional comparison.

Source motivation: GLS3, Table 5.3i, printed p.270. Source matrices and
the original ATLAS word program are attributed in `Max2Bridge` and its
`source/` directory. The table itself supplies none of the proof premises.
-/

public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

/-- The concrete order bounds imply generation of the entire centralizer.
All three bounds, including those for actors outside the word subgroup,
must be discharged before this gives an unconditional generation theorem. -/
theorem localSubgroup_eq_top_of_homology_bounds
    (hlower : 21799895040 ≤ Nat.card sourceSubgroup)
    (hkernel : Nat.card Generation.homologyAction.ker ≤ 8192)
    (himage : Nat.card Generation.homologyAction.range ≤ 2661120) :
    localSubgroup = ⊤ :=
  localSubgroup_eq_top_of_card_bounds hlower
    (Generation.centralizer_card_le_of_homology_bounds hkernel himage)

/-- The certified conjugates of the two ATLAS max2 outputs generate the
entire literal centralizer `matrixGroup ⊓ Subgroup.centralizer {matrixUnitA}`. -/
theorem localSubgroup_eq_top : localSubgroup = ⊤ :=
  localSubgroup_eq_top_of_homology_bounds sourceSubgroup_card_ge
    Generation.homologyAction_kernel_card_le Generation.homologyAction_image_card_le

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
