module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Normalizers

/-!
# Sylow and Borel calculations for the concrete PSL₃ flag model

The actual UT₃ coordinate embeddings identify the intersection of the two
local factors with a Sylow two-subgroup when the field has order `2^n`, `n>0`.
Its order is `q^3`; the ambient order and index retain the scalar divisor
`gcd(3,q-1)`. Its full normalizer is the flag Borel. Restriction to each local
factor gives the corresponding local Sylow and relative normalizer.
For `q>2` the Borel strictly contains the Sylow subgroup.

Source: Aschbacher–Smith, F.1.12(I)(1), printed pp.262–264.
The local block structure and final source-amalgam assembly are separate.
-/
