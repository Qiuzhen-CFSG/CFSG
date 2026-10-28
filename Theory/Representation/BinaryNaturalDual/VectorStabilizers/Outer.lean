module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Outer.Orders
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Outer.Recognition
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Outer.Sylow

/-!
# The full nonsingular natural-plus-dual stabilizer

For every pairing-one pair in the specified actual automorphism action, its
full stabilizer is the split extension of the inner stabilizer by an outer
involution. Conjugation on the actual kernel group identifies this extension
with Aut(PSL in one lower dimension), compatibly with the published inner map.
The natural-to-dual block explicitly intertwines the kernel conjugation action
with its contragredient. The embedded two-residual is the inner stabilizer.

The orders are 336 and 40320 in dimensions four and five. Every actual Sylow
two-subgroup of this stabilizer contains an outer involution giving the same
split extension. None of these assertions retains the incompatible global
Sylow marking of the earlier pure-vector clause.

Source: Aschbacher–Smith, H.9.1(4), printed pp.389–390, with the corrected
nonsingular statement specified by the H.9 source audit of 6 October 2026.
-/
