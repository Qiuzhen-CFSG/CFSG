module

public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Geometry
public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Equivariance
public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Transport

/-!
# Adapted-pair geometry and simultaneous actor transport

The geometric moving space, fixed-vector spaces and standard coordinate
objects are defined in `Geometry`. `Equivariance` transports their actual
linear actions. `Transport` proves the index-two and Sylow arguments that
preserve a specified actor while moving a point.

The explicit standard subgroup calculations in dimensions four and five
are separate obligations. These imports alone do not prove the corrected
H.9.1(4) adapted-pair theorem.
-/
