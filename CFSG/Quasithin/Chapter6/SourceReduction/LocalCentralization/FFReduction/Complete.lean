module

public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction.BaumannControl
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction.ResidualMovement

/-!
# The complete local Cartan FF reduction

The original rank-one Baumann normalizer bound supplies the last earlier
input to the FF construction, at the same ambient group and original reduced
module. Exceptional overcomponent preservation is already discharged in that
construction. Thus failure of omega-centralization produces the literal maximal
A₇ configuration, with both Thompson equalities, the irreducible omega-module
of order 16 or 64, its splitting and fixed-space vanishing, and movement by the
original residual.

Source: Aschbacher--Smith 5.1.13, printed p.637, using 5.1.7(1), pp.633--634.
-/

public section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The original FF reduction with all its earlier source inputs proved. -/
theorem localCartan_ffReduction : LocalCartanFFReduction G :=
  localCartan_ffReduction_source rankOneBaumannNormalizerControl_source

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
