module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Source

/-!
# Local action and geometry in the large extraspecial branch

This interface exports the constructed full conjugation action, component
selection and placement for every member of the source Y-family. Cubic
indices identify both actual whole parabolics without assumed markings.
The three-vertex assembly derives the literal intersections, the residual
O²(L∩H₃)=L₂ and the relative normalizer, and supplies the D-system on the
actual generated subgroup G₀ using the existing intrinsic construction.

`source_lemma_14_4_8` constructs both clauses from the actual natural action,
the original invariant flag and the explicit earlier 12.8/14.3/1.2.1 inputs.
`source_geometry_of_source_flag` applies it to the two surviving family
members and constructs the ambient geometry from the sibling middle quotient
and the earlier normality and uniqueness clauses for M. No natural-flag
conclusion, marked maximality or A₃ certificate is an input. The outer
source assembly retains discharge of the earlier and sibling premises from
Hypothesis 14.3.10, and the recognition of G₀. All earlier conditional
interfaces, including `source_dSystem_of_marked_maximality`, remain available.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
14.4.8 and 14.4.13, printed pp.1009,1012. I₂ is distinguished from I₂T,
and the whole intersection from its two-residual.
-/
