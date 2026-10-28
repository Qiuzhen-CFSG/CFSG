module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Action
public import Theory.Representation.BinaryConjugationSection
public import Theory.Representation.SpecialLinearNatural

/-!
# Independent source branches of the constrained exclusion

The first obligation supplies the point-orbit centralizer and Thompson facts.
The second performs the embedding and module analysis on that actual action:
the torus and A7 alternatives are removed, leaving the binary linear-five
irreducible of dimension five or ten. The third proves the two terminal
parabolic contradictions. It can take the linear-five data explicitly while
the first two obligations are being proved. Final assembly must discharge all
three; none is a theorem asserted by this module.

The retained four-natural row of 10.1.1(6) must be handled in the first two
obligations without using the generation bound invoked by source 10.2.7.
Source: Aschbacher--Smith, 10.2.9, printed pp.751--753.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The actual terminal configuration on p.752, before the two parabolic
contradictions. The original component, quotient map, and orbit module remain
fixed. This is a conclusion to construct, not an assumption of point control. -/
structure LinearFiveData (c : Context D t v I) where
  quotient : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
  natural : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
    ((specialLinearNatural 3).comp
      (quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))
  sylow_eq : pointSylow T v = (T : Subgroup G) ⊓ normalizer (L : Set G)
  moved_le : ⁅D.fullModule,L⁆ ≤ orbitModule D v I
  actor : letI := c.reduced.normal
    ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) ≃*
      Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)
  actor_eq_top : letI := c.reduced.normal
    (I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I)) = ⊤
  kernel_eq : letI := c.reduced.normal
    ((actionMk (internalModule D v I)).subgroupMap (I.subgroupOf (pointJoin T v I))).ker =
      pCore 2 (I.subgroupOf (pointJoin T v I))
  irreducible : letI := c.reduced.normal; letI := c.reduced.elementary
    Representation.IsIrreducible ((action (internalModule D v I)).comp
      ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))).subtype)
  dimension : letI := c.reduced.elementary
    Module.finrank (ZMod 2) (Additive (internalModule D v I)) = 5 ∨
      Module.finrank (ZMod 2) (Additive (internalModule D v I)) = 10

/-- Source preparation, including the exceptional fixed-layer possibility. -/
def PreparationAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (t v : G) (I : Subgroup G), Context D t v I → Prepared D v I

/-- The torus obstruction, A7 analysis, and reduction to the two original
linear-five irreducibles. No model-inspection callback is part of the result. -/
def LinearFiveReductionAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (t v : G) (I : Subgroup G) (c : Context D t v I),
    ActionFacts c → Nonempty (LinearFiveData c)

/-- The original rank-five and rank-ten parabolic endgame, conditional only
on the displayed source configuration and its actual linear-five reduction. -/
def LinearFiveExclusionAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (t v : G) (I : Subgroup G) (c : Context D t v I),
    ActionFacts c → LinearFiveData c → False

end CFSG.Quasithin.Chapter10.PointControl.Constrained
