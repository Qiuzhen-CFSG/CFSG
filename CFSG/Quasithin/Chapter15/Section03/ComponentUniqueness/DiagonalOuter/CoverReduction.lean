module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.ModelWitnesses
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalAlgebra
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.TransferGeometry
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly

/-!
# The central-cover reduction in 15.3.38

`Assembly.cover_reduction` constructs the marked L₃(4) central cover from the
genuine contrary rank-two setup and uniform earlier source conclusions. It
identifies its centre and both local centralizers, proves the literal product,
and repeats the reduction in the full centre normalizer. Containment and the
actual cover orders identify the larger component and its opposite residual.

The outer-action order bound identifies C_T(V) with O₂(Y)=S∩L. Compatible
relabelling of the natural planes then supplies the Sylow-three normalizer,
its graph and field involutions and its dihedral section. The rotation
preimage is literally W=⟨w,S_L⟩ and has an actual cyclic-four quotient with
the exact kernel. The representative-centralizer bound, transitive actor,
ordinary graph-centralizer component, normalizer action and kernel are also
constructed. `Assembly.Reduction.field_fusion` feeds these witnesses into the
published transfer reduction.

This completes the conditional geometric reduction. The explicit intrinsic
inputs are the Sylow centralizer bound, graph/field coset recognition, graph
residual model and local odd-core model. The precise earlier balance and
embedding theorems, M₂₃ multiplier and standing local source conclusions also
remain inputs. Final 15.3.38 assembly and discharge of these inputs belong to
`DiagonalOuter`; no numbered source theorem is asserted here.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
proof of 15.3.38, printed pp.1135--1137.
-/
