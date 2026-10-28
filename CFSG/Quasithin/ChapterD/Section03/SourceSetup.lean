module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Statement
public import Theory.Representation.BinaryOffender.Homogeneous.Basic
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Mathlib.GroupTheory.Frattini
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The original module hypotheses D.3.1

The module is faithful for the actual quotient of an SQTK group. Its
normal actor is either the Sylow orbit of an ordinary component, or an
odd-prime group with irreducible conjugation on its Frattini quotient.
The seed is a genuine Irr⁺ member, invariant under the two-core of M⁺T,
and its M-orbit spans the original module.

No conclusion of D.3.3 or D.3.4 is imposed in these hypotheses.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Hypothesis D.3.1, printed p.193.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.ChapterD.Section03
universe u v
variable {G : Type u} [Group G]

/-- Literal conjugation on the Frattini quotient of a normalized subgroup. -/
def frattiniAction (T X : Subgroup G) (hTX : T ≤ normalizer (X : Set G)) :
    T →* MulAut (X ⧸ frattini X) :=
  (quotientAut (frattini X)).comp (X.normalizerMonoidHom.comp (inclusion hTX))

/-- Irreducibility on the original Frattini quotient, expressed by its
invariant subgroups. For a p-group these are exactly its vector subspaces. -/
def FrattiniIrreducible (T X : Subgroup G) (hTX : T ≤ normalizer (X : Set G)) : Prop :=
  ∀ A : Subgroup (X ⧸ frattini X),
    (∀ t : T, ∀ a ∈ A, frattiniAction T X hTX t a ∈ A) → A = ⊥ ∨ A = ⊤

/-- The two original structural alternatives in D.3.1. -/
def ActorCases (T : Sylow 2 G) (X : Subgroup G)
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G)) : Prop :=
  (∃ L : Subgroup G, IsComponent G L ∧ X = componentOrbit L (T : Subgroup G)) ∨
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ IsPGroup p X ∧
      FrattiniIrreducible (T : Subgroup G) X hTX)

/-- Hypothesis D.3.1, with the actual covering quotient and orbit span. -/
structure SourceHypotheses (K : GroupClass.{u}) [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G)
    (X : Subgroup G) (I : Submodule (ZMod 2) V) : Prop where
  sqtkQuotient : Nonempty (ChapterB.SourceInduction.SQTKQuotient K G)
  finiteModule : Module.Finite (ZMod 2) V
  faithful : Function.Injective ρ
  normal : X.Normal
  cases : ActorCases T X (by rw [normalizer_eq_top]; exact le_top)
  seed : IsIrrPlus ρ X I
  coreInvariant : (X ⊔ (T : Subgroup G)).pCoreIn 2 ≤ subspaceStabilizer ρ I
  generated : orbitSpan ρ ⊤ I = ⊤

end CFSG.Quasithin.ChapterD.Section03
