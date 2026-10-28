module

public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.PairedBorel.Elementary
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.PairedBorel.Summands
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.PairedBorel.Marking

/-!
# The concrete swapped paired-A₅ Borel calculation

This interface exports the faithful action on the two orthogonal cores, the
specified elementary subgroup of order eight, the actual A₄-product point
stabilizer, and the two-residual calculation for its concrete overgroups.
Two-perfectness and three-rank of A₄ × A₄ remain explicit numerical inputs.

Block isometry recognition and elementary subgroup conjugacy now construct
compatible full-group, factor, swap and Sylow markings from the geometric
action and source splitting clause. The terminal consumer uses them to
identify the residual inside the original faithful quotient.

Source: Aschbacher–Smith, G.11.2(12) and 12.8.13(7), combined manuscript
of 1 March 2004, printed pp.364 and 855–856.
-/
