module
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.FourAt
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledInterface

/-!
# Original structural source after the complete doubled exclusion

The complete marked non-FF doubled argument is supplied internally at the
same original group and Sylow subgroup. The genuine nonnormal reduction and
rank-one generic/small exits remain explicit. No module-classification or
doubled-row callback is introduced.
Source: Aschbacher--Smith 12.2.2, printed p.795.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.SourceAssembly.At
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The original structural conclusion with all doubled rows discharged. -/
theorem structural1222At_after_original_doubled_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hreduction : Chapter10.SourceNonnormalReductionAt T)
    (hgeneric : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      ChosenModule T L V → ∀ n, 1 < n →
      ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n) →
      RankOneModule.GenericConfigurationExit T L)
    (hsmall : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      ChosenModule T L V → ∀ n, 1 < n →
      ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n) →
      RankOneModule.SmallExit T L) : Structural1222At KnownSimple.IsKnownSimple T :=
  structural1222At_after_original_four_of_many hmany hreduction
    (fun _ _ h D => D.sourceOrbit_nonFF_doubled_excluded_original h hmany)
    hgeneric hsmall
end CFSG.Quasithin.Chapter12.Section02.SourceAssembly.At
