module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Actors.Source
public import Theory.SpecificGroups.MinusExtraspecial.CubicNorm
public import Theory.SpecificGroups.MinusExtraspecial.CubicAction.NormalForm

/-!
# Source normalizer actors from the earlier local geometry

The source 47.1–47.2 geometry supplies the actual A₅ embedding and the
inverting involution. The finite core-norm theorem constructs an independent
order-eight actor with the literal membership and order required by
`CentralizerCalculation`.

The checked cubic normal form discharges the finite action premise on the
actual extraspecial group. `normalizer_actors` therefore needs only the
earlier 47.1–47.2 conclusions, with no semidihedral structure or 47.3
identification. The conditional normal-form interface is preserved below.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.3, p.262.
-/

public section
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
variable {G : Type*} [Group G] [Finite G] {D : Seed G}

/-- The exact source actors, conditional only on the independent finite
cubic-normal-form theorem in addition to the earlier source conclusions. -/
theorem EarlierConclusions.actors_of_cubicNormalForm (E : EarlierConclusions D)
    (hNF : MinusExtraspecial.CubicAction.HasCubicNormalForm) :
    (∃ m : M D, orderOf m = 2 ∧
      ∀ x : D.X, (m : G) * x * (m : G)⁻¹ = (x : G)⁻¹) ∧
    (∃ s : M D, orderOf s = 8) :=
  E.actors_of_core_norm
    (MinusExtraspecial.FixedFourCalculation.CubicNorm.norm_four_of_cubicNormalForm hNF)

/-- The order-two inverter and an independent order-eight element of the literal
normalizer, constructed using only the earlier 47.1–47.2 conclusions. -/
theorem EarlierConclusions.normalizer_actors (E : EarlierConclusions D) :
    (∃ m : M D, orderOf m = 2 ∧
      ∀ x : D.X, (m : G) * x * (m : G)⁻¹ = (x : G)⁻¹) ∧
    (∃ s : M D, orderOf s = 8) :=
  E.actors_of_cubicNormalForm MinusExtraspecial.CubicAction.hasCubicNormalForm

/-- The earlier source geometry supplies the order-eight actor required by
the extension recognition, without an additional finite-model premise. -/
theorem EarlierConclusions.exists_order_eight (E : EarlierConclusions D) :
    ∃ s : M D, orderOf s = 8 :=
  E.normalizer_actors.2

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
