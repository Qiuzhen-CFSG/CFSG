module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.Seed
public import Theory.SpecificGroups.BinaryLinear.Parabolics

/-!
# Module conclusions in the L₄ chief-factor argument

These predicates retain a single identification of the actor with GL₄(2),
actual linear equivalences, and the intertwining identities. Chief factors
are literal quotients of consecutive invariant subspaces. Thus different
quotients cannot silently use unrelated automorphisms of the actor, and a
central factor means a trivial action on that quotient.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), 13.8.25, printed pp.960–961. These are specifications
of the intermediate conclusions, not assumptions proving the source theorem.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
open Representation Representation.BinaryOffender

abbrev NaturalSpace := Fin 4 → ZMod 2

variable {H E U : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup U] [Module (ZMod 2) U]

/-- The actual action through a specified group identification. -/
def naturalAction (e : H ≃* BinaryLinear.GL E) : Representation (ZMod 2) H E where
  toFun g := (e g).toLinearMap
  map_one' := by rw [map_one]; rfl
  map_mul' g h := by simp

/-- Equivalence with the natural module for this particular actor identification. -/
def IsNatural (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) : Prop :=
  ∃ e : U ≃ₗ[ZMod 2] NaturalSpace, ∀ g u, e (ρ g u) = eH g (e u)

/-- Natural and contragredient actions, with the same actor identification. -/
def IsNaturalOrDual (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) : Prop :=
  IsNatural ρ eH ∨
    ∃ e : U ≃ₗ[ZMod 2] Module.Dual (ZMod 2) NaturalSpace,
      ∀ g u, e (ρ g u) = (naturalAction eH).dual g (e u)

/-- All maximal quotients have compatible natural identifications. -/
def AllNaturalHeads (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) : Prop :=
  ∀ W : Subrepresentation ρ, IsCoatom W → IsNatural W.quotientRepresentation eH

/-- A central section has trivial action on the literal quotient. -/
def IsCentralSection (ρ : Representation (ZMod 2) H U)
    (A B : Subrepresentation ρ) : Prop :=
  ∀ g v, sectionRepresentation ρ A B g v = v

/-- Only noncentral chief factors are classified at this stage. -/
def NoncentralChiefFactorsNaturalOrDual (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) : Prop :=
  ∀ A B : Subrepresentation ρ, A ⋖ B → ¬ IsCentralSection ρ A B →
    IsNaturalOrDual (sectionRepresentation ρ A B) eH

/-- The conclusion after the cohomology step, including absence of central factors. -/
def ChiefFactorsNaturalOrDual (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) : Prop :=
  ∀ A B : Subrepresentation ρ, A ⋖ B →
    IsNaturalOrDual (sectionRepresentation ρ A B) eH ∧ ¬ IsCentralSection ρ A B

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
