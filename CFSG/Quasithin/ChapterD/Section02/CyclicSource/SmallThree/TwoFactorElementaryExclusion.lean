module
public import Theory.Representation.BinaryOffender.FourDimensionalCubic
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.LinearBudget

/-!
# Excluding four-subgroups with two canonical cubic supports

The actual sum of the two marked support planes has dimension four.
The generic cubic-ratio obstruction therefore excludes an elementary
four-subgroup of the original actor. This supplies the Sylow argument
in Aschbacher--Smith D.2.25, printed p.190.
-/


namespace CFSG.Quasithin.ChapterD.CyclicSource.SmallThree
open Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

public theorem supportFactors_two_no_elementary_four {P : Subgroup G}
    (d : FittingConfigurations.SupportFactors ρ P 2) (hratio : cubicRatio ρ = 2)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) : Nat.card A ≠ 4 := by
  have hd : Module.finrank (ZMod 2) V = 4 := by simpa using d.finrank_eq ρ
  exact no_elementary_four_of_four_dimensional_cubicRatio_two ρ hd hratio A hA
end CFSG.Quasithin.ChapterD.CyclicSource.SmallThree
