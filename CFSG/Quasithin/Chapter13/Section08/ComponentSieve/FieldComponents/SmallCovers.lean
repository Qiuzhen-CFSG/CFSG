module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.ThreeDimensional

/-!
# Small-cover branches of 13.8.21(2)

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, printed pp.955–956, PDF pp.972–973.

`Basic` proves the irreducible-seed/fixed-line contradiction for the M₂₂
branch, the rank-two saturation of a four-group, and relative normality
and normalizer consequences for the actual Y = O²(O₂,Z(K)). The parabolic
placement and code-module comparisons, the solvable-overgroup exclusion of
Y = L₁, reduction through the actual K₁ and recognition of the six-dimensional
module remain to be supplied before these deductions prove the source clause.

`ThreeDimensional` verifies a restriction on the terminal proof route:
every elementary two-subgroup of the genuine even hexacode cover is
quadratic on its six-dimensional binary module. If a subgroup of the full
hexacode group contains the cubic scalar, its two-core lies in the even
cover. Thus an elementary two-core of the F₄-point stabilizer is quadratic
on this quotient module. Nonquadraticity on this module is not an available
intrinsic input. The full source configuration or its actual extension must
supply the terminal contradiction. Source 13.8.4(6) asserts quadraticity on
Ũ_H and V_H/U_H; it does not by itself assert quadraticity on U_H.

No numbered source exclusion is claimed here. Final assembly must preserve
the L₃(2) alternative in the statement of 13.8.21(2), even though the first
sentence of its printed proof omits it. All new prerequisites import `Basic`
and the narrow source modules directly, leaving this module as assembly owner.
-/
