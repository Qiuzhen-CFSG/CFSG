module

public import CFSG.Quasithin.Chapter12.Section08.Defs
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Residuals

/-!+# Interfaces for the normalizer projection in 14.7.70

The first interface describes an actual homomorphism on M = N_G(L),
extending the original quotient map on L. Its point and line images are
the embedded two-residuals of the parabolics (A₄), not the whole S₄
parabolics. The normalizer lifting clause concerns the actual L₁.
Constructing this interface from the earlier natural-module setup is a
separate obligation; its fields are not asserted source theorems.

The second interface is a finite-group implication for arbitrary maps
X → S₃ and X → SL₃(2). The two-group kernel bounds the order of the
second image. The Borel overgroup calculation then selects the line
parabolic and detects a nontrivial action through the first map.
It has no Chapter 14 escape conclusion. Its model proof and the first
interface's constructor are independent obligations. The importing escape
assembly must supply both before this stage is complete.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
Notation 14.7.1, printed p.1043, and Lemma 14.7.70, printed p.1074.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape
open Chapter12.Section08 Matrix.PSL3Two
universe u

/-- Intermediate construction target, independent of the critical path.
The extension equation retains the literal L → L/O₂(L) quotient. -/
structure NormalizerProjection {G : Type u} [Group G] (T : Sylow 2 G)
    (L V : Subgroup G) (F : InvariantFlag T V 3) where
  quotientEquiv : (L ⧸ pCore 2 L) ≃* SL
  project : normalizer (L : Set G) →* SL
  on_L : project.comp (inclusion L.le_normalizer) =
    quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  sylow_le : (T : Subgroup G) ≤ normalizer (L : Set G)
  inner_sylow_image : (((T : Subgroup G) ⊓ L).subgroupOf
    (normalizer (L : Set G))).map project = borelSL
  point_image : ((F.Li L 1).subgroupOf (normalizer (L : Set G))).map project =
    MarkedAutomorphisms.pointA
  line_image : ((F.Li L 2).subgroupOf (normalizer (L : Set G))).map project =
    MarkedAutomorphisms.lineA
  lift_point_normalizer :
    (normalizer (MarkedAutomorphisms.pointA : Set SL)).comap project ≤
      (normalizer (F.Li L 1 : Set G)).subgroupOf (normalizer (L : Set G))

/-- The precise independent finite model implication needed by the assembly.
The conclusion names the residual line subgroup of order twelve. -/
def ParabolicImageTheorem : Prop :=
  ∀ (X : Type u) [Group X] [Finite X]
    (f : X →* Equiv.Perm (Fin 3)), Function.Surjective f → IsPGroup 2 f.ker →
    ∀ (π : X →* SL) (A : Subgroup X), A.map π = borelSL →
      (¬ (pResidual 2 X).map π ≤ normalizer (MarkedAutomorphisms.pointA : Set SL)) →
      (pResidual 2 X).map π = MarkedAutomorphisms.lineA ∧ ¬ A ≤ f.ker

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness.ProjectionEscape
