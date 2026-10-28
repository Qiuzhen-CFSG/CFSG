module

public import Theory.Representation.BinaryOffender.Defs
public import Mathlib.GroupTheory.Sylow

/-!
# Root-group inputs for the inner SU₃ degree estimate

The root group used here is the embedded center of an actual Sylow
two-subgroup. `RootControl` states containment of every elementary actor
in such a center, its order, and irreducibility of its normalizer action.
`ThreeRootGeneration` asks for three actual conjugates generating the group.
These are independent group-theoretic obligations, with no representation
or degree conclusion in either definition.

`InnerActors.Reduction` uses offender maximization and the intersection of
three conjugate fixed spaces to deduce the binary degree bound from them.
The concrete SU₃ geometry is not asserted by this module.

Source: Huppert II.10.12 for the Hermitian root coordinates; Guralnick--Malle,
Classification of 2F-modules II, Lemma 2.1, and the fixed-space generation
inequality used in Aschbacher--Smith K.1, printed pp.451--453.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
namespace Representation.SU3.CubicDegree.InnerActors

/-- The center of a Sylow two-subgroup, embedded in its actual ambient group. -/
noncomputable def sylowCenter {G : Type*} [Group G] (P : Sylow 2 G) : Subgroup G :=
  (center P).map (P : Subgroup G).subtype

/-- Elementary actors lie in root groups of order `2^s` on which the
normalizer has no proper nontrivial invariant subgroup. -/
def RootControl (G : Type*) [Group G] (s : ℕ) : Prop :=
  ∀ A : Subgroup G, IsElementaryTwo A →
    ∃ P : Sylow 2 G, A ≤ sylowCenter P ∧ Nat.card (sylowCenter P) = 2 ^ s ∧
      ∀ B ≤ sylowCenter P, B ≠ ⊥ →
        normalizer (sylowCenter P : Set G) ≤ normalizer (B : Set G) → B = sylowCenter P

/-- Three literal inner conjugates of each Sylow center generate the group. -/
def ThreeRootGeneration (G : Type*) [Group G] : Prop :=
  ∀ P : Sylow 2 G, ∃ c : Fin 3 → G,
    (⨆ i, (sylowCenter P).map (MulAut.conj (c i)).toMonoidHom) = ⊤

end Representation.SU3.CubicDegree.InnerActors
