module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.Preparation
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.ModelInput

/-!
# Remaining source geometry for the H-star fixed-seed module

These two source obligations identify the literal H/C_H(U) and establish that
H∩M fixes Ω₁Z(T). The latter follows in the source from parabolic placement of
O²(H∩M), centralization of Ω₁Z(T) by L₀, and the Sylow/residual supplement.
Earlier-source Hall faithfulness is explicit, so this argument can be proved
independently of its producer and discharged by the final assembly owner.
Neither conclusion assumes a module parameter, fixed-space vanishing, or TI.
Source: Aschbacher--Smith 10.2.3(3), 10.2.8(1), and 10.3.1, pp.745,749,755.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)

/-- The precise group-theoretic and fixed-seed input to the independent module calculation. -/
def QuotientGeometryAt : Prop :=
  SourceNonnormalHallFaithfulAt T →
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (_s : SourceLinearThreeSurvivor T D),
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥ →
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal,
      Nonempty (OmegaQuotient T H ≃*
        Theory.SpecificGroups.SymmetricFive.WreathComponents.W) ∧
      H ⊓ D.maximalLocal ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter
