module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.Contracts

/-!
# The three further-enlargement obligations in E.6.23

An escaping conjugate supplies the intersection A₁ = A ∩ Uᵍ. The first
obligation constructs a strictly larger component, normal inside C_G(A₁).
The second identifies that component with an actual projective linear group
and retains the order-two outer action induced by A. The third constructs
the corank-two subspace inducing a two-central involution and proves that
A centralizes no Sylow two-subgroup of the component.

These are outstanding mathematical contracts, not proved source results.
All action images use conjugation on the actual embedded subgroup. None of
the contracts assumes the disputed residual containment for C_G(A₂).
`SixAutomorphisms` owns their discharge and the final orbit containment.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.254
(PDF p.265), the further-enlargement paragraph in the proof of E.6.23.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms
open ComponentBalance

variable {G : Type*} [Group G]

/-- The actual corank-at-most-three subspace used for further enlargement. -/
abbrev intersection (A U : Subgroup G) (g : G) : Subgroup G :=
  A ⊓ U.map (MulAut.conj g).toMonoidHom

/-- Exactly the input to `SixOrbitContainment`, with one contrary conjugate.
No conclusion about the new component or its action is included. -/
structure EscapeConfiguration (M V U A L X : Subgroup G) (g : G) : Prop where
  hyperplane_mem : U ∈ obstructionFamily M V
  hyperplane : IsHyperplane V U
  block : SmallBlock U L
  escapes : ¬ L ≤ M
  subspace_mem : A ∈ obstructionFamily M V
  subspace_le : A ≤ U
  corank : subgroupCorank V A = 2
  six : ProperSixEnlargement V U A L X
  conjugator_mem : g ∈ localNormalizer M V
  conjugate_escapes : ¬ L.map (MulAut.conj g).toMonoidHom ≤ X

/-- The desired containing component is normal only in C_G(A ∩ Uᵍ). -/
structure NormalComponentExtension (U A X : Subgroup G) (g : G)
    (Y : Subgroup G) : Prop where
  proper : X < Y
  component : CentralizerComponent (intersection A U g) Y
  normal : (Y.subgroupOf (centralizer (intersection A U g : Set G))).Normal

/-- The subgroup of Aut(Y) induced by the elements of D which normalize Y.
In every application below, relative normality proves that all of D normalizes Y. -/
def actionImage (D Y : Subgroup G) : Subgroup (MulAut Y) :=
  (D.subgroupOf (normalizer (Y : Set G))).map Y.normalizerMonoidHom

/-- Genuine L₄(2)/L₅(2) identification, together with the actual outer involution. -/
structure LinearModelAction (A Y : Subgroup G) : Prop where
  model : ClassicalGroup.IsPSL Y 4 2 ∨ ClassicalGroup.IsPSL Y 5 2
  order_two : Nat.card (actionImage A Y) = 2
  outer : ¬ actionImage A Y ≤ (MulAut.conj : Y →* MulAut Y).range

/-- The two model facts consumed by the terminal Sylow argument. Order two
of the induced subgroup and an actual fixed Sylow subgroup express precisely
the two-central involutory action of the constructed subspace. -/
structure TwoCentralGeometry (V A₁ A Y : Subgroup G) : Prop where
  no_fixed_sylow : ∀ P : Sylow 2 Y,
    ¬ (P : Subgroup Y).map Y.subtype ≤ centralizer (A : Set G)
  subspace : ∃ B : Subgroup G, A₁ ≤ B ∧ B ≤ V ∧ subgroupCorank V B = 2 ∧
    Nat.card (actionImage B Y) = 2 ∧
      ∃ P : Sylow 2 Y, (P : Subgroup Y).map Y.subtype ≤ centralizer (B : Set G)

/-- I.3.1 and the strictness argument, with the nonidentity intersection supplied. -/
def FurtherLift (M V : Subgroup G) : Prop :=
  ∀ U A L X : Subgroup G, ∀ g : G, EscapeConfiguration M V U A L X g →
    intersection A U g ≠ ⊥ → ∃ Y : Subgroup G, NormalComponentExtension U A X g Y

/-- The outstanding model inspection; its conclusion includes actual isomorphisms. -/
def ModelIdentification (M V : Subgroup G) : Prop :=
  ∀ U A L X : Subgroup G, ∀ g : G, EscapeConfiguration M V U A L X g →
    intersection A U g ≠ ⊥ → ∀ Y : Subgroup G, NormalComponentExtension U A X g Y →
      LinearModelAction A Y

/-- The remaining action calculation may be proved independently with the
identified model and outer involution supplied as explicit hypotheses. -/
def LinearActionAnalysis (M V : Subgroup G) : Prop :=
  ∀ U A L X : Subgroup G, ∀ g : G, EscapeConfiguration M V U A L X g →
    intersection A U g ≠ ⊥ → ∀ Y : Subgroup G, NormalComponentExtension U A X g Y →
      LinearModelAction A Y → TwoCentralGeometry V (intersection A U g) A Y

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms
