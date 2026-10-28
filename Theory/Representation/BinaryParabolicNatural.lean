module

public import Theory.Representation.BinaryParabolicNatural.Basic
public import Theory.Representation.BinaryParabolicNatural.CentralCovers

/-!
# Natural and dual binary parabolic calculations

The geometric radical fixed spaces, component commutators, equivariant
coordinates, finite direct sums and explicit matrix actions used in the
natural/dual part of Aschbacher--Smith C.4.8 (printed p.154).

The basic module constructs both full end-parabolic markings and proves the
calculation for components with marked block actions. CentralCovers eliminates
the natural/dual central kernels in B.5.1(i), splits off globally fixed summands,
and applies the calculation to the original covering maps. Identification of
all source perfect components, in particular the middle parabolics, remains
an assembly input; no module conclusion is assumed in the group markings.
-/
