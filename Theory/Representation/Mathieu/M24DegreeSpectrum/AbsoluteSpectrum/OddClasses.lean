module

public import Theory.Mathieu.M24.Properties.OddClasses
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.Contracts

/-!
# The native odd-class certificate for the absolute M₂₄ spectrum

The checked thirteen-representative argument, native odd-order spectrum and
mixed-order coverage supply the literal `OddClassBound` contract. All coverage
premises are discharged by proofs on the actual Witt-design carrier.

The consumer is `absoluteSmallSpectrum_of_models` in `AbsoluteSpectrum`:
`oddClassBound` discharges its conjugacy-class bound input. The independent
small and large representation families remain with that assembly's owner.

Source: Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1,
manuscript p.17; native ATLAS M24 conjugacy data.
-/

namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum
open Sporadic.Mathieu

/-- The concrete group calculations discharge the absolute-spectrum class bound. -/
public theorem oddClassBound_of_calculations
    (hspectrum : M24OddCyclic.OddOrderSpectrum)
    (hmixed : M24OddCyclic.MixedOrderCyclicCoverage) : OddClassBound :=
  M24OddClasses.oddClassBound_of_calculations hspectrum hmixed

/-- The unconditional native odd-class bound required by the spectrum consumer. -/
public theorem oddClassBound : OddClassBound :=
  M24OddClasses.oddClassBound

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum
