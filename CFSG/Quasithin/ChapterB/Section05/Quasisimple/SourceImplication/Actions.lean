module

public import CFSG.Quasithin.Defs
public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.BinaryPermutation
public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.Representation.BinaryOffender.IrreducibleSection
public import Theory.Representation.SymplecticNatural
public import Theory.Representation.G2Natural

/-!
# Native actions for B.5.1

Group identifications and binary linear intertwiners retain the original action.
Repeated natural modules use one identification of the actor on all summands.
These are lower-layer definitions for the source implication, independent of
Chapter 15. They match the mathematical action conventions of its consumer.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, B.4.2 and B.5.1, printed pp.86 and 99–103.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
universe u v w z

/-- A finite field of order 2ⁿ with the positive exponent retained. -/
structure BinaryField where
  Carrier : Type
  [field : Field Carrier]
  [finite : Finite Carrier]
  [charTwo : CharP Carrier 2]
  [binaryAlgebra : Algebra (ZMod 2) Carrier]
  degree : ℕ
  degree_pos : 0 < degree
  card_eq : Nat.card Carrier = 2 ^ degree

attribute [instance] BinaryField.field BinaryField.finite BinaryField.charTwo
  BinaryField.binaryAlgebra

/-- The binary prime field, used for the exceptional four-dimensional cases. -/
def BinaryField.two : BinaryField where
  Carrier := ZMod 2
  degree := 1
  degree_pos := by decide
  card_eq := by simp

/-- An isomorphism of the group and its actual representation together. -/
structure ActionEquiv {D : Type u} {E : Type v} [Group D] [Group E]
    {V : Type w} {W : Type z} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D V) (σ : Representation (ZMod 2) E W) where
  groupEquiv : D ≃* E
  linearEquiv : V ≃ₗ[ZMod 2] W
  intertwines : ∀ g v, linearEquiv (ρ g v) = σ (groupEquiv g) (linearEquiv v)

variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- The matrix action, restricted to the binary prime field. -/
def linearNatural (F : BinaryField) (d : ℕ) :
    Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin d) F.Carrier)
      (Fin d → F.Carrier) :=
  restrictScalars (k := ZMod 2) (specialLinearNatural d)

/-- The same representation on each of r summands. -/
def repeated (r : ℕ) : Representation (ZMod 2) D (Fin r → V) where
  toFun g :=
    { toFun := fun v i => ρ g (v i)
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  map_one' := by
    apply LinearMap.ext
    intro v
    funext i
    exact LinearMap.congr_fun ρ.map_one (v i)
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    funext i
    exact LinearMap.congr_fun (ρ.map_mul g h) (v i)

/-- A natural SL module, including an actual group identification. -/
def IsLinearNatural (F : BinaryField) (d : ℕ) : Prop :=
  Nonempty (ActionEquiv ρ (linearNatural F d))

/-- Repeated copies of one and the same natural representation. -/
def IsRepeatedLinearNatural (F : BinaryField) (d r : ℕ) : Prop :=
  Nonempty (ActionEquiv ρ (repeated (linearNatural F d) r))

/-- A natural symmetric-group module in the deleted permutation model. -/
def IsSymmetricNatural (n : ℕ) : Prop :=
  Nonempty (ActionEquiv ρ (BinaryPermutation.naturalRepresentation (Fin n)))

/-- Indecomposability is measured in the lattice of invariant subspaces. -/
def IsIndecomposable : Prop :=
  Nontrivial V ∧ ∀ A B : Subrepresentation ρ,
    IsCompl A.toSubmodule B.toSubmodule → A = ⊥ ∨ B = ⊥

/-- The actual commutator [V,A]. -/
abbrev moved (A : Subgroup D) : Submodule (ZMod 2) V :=
  subspaceCommutator ρ ⊤ A

/-- The fixed subrepresentation C_V(D). -/
noncomputable def fixed : Subrepresentation ρ where
  toSubmodule := ρ.invariants
  apply_mem_toSubmodule g v hv := by
    change ∀ h, ρ h (ρ g v) = ρ g v
    rw [hv g]
    exact hv

/-- The faithful source convention Ṽ = V/C_V(D), with its induced action. -/
noncomputable abbrev reducedAction := (fixed ρ).quotientRepresentation

/-- B.4.8(3)'s exceptional extension: dimension four, indecomposable,
with its three-dimensional commutator a genuine natural SL₃(2)-module. -/
def IsFourDimensionalExtension : Prop :=
  Module.finrank (ZMod 2) V = 4 ∧ IsIndecomposable ρ ∧
  ∃ W : Subrepresentation ρ, W.toSubmodule = moved ρ ⊤ ∧
    Nonempty (ActionEquiv W.toRepresentation (specialLinearNatural (k := ZMod 2) 3))

end CFSG.Quasithin.ChapterB.QuasisimpleSource
