module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.Inputs
public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.BinaryPermutation
public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.Representation.BinaryOffender.IrreducibleSection

/-!
# Actual modules used in the B.5 alternatives

An identification consists of a group isomorphism and an intertwining binary
linear equivalence. Natural modules are the concrete matrix or deleted
permutation representations. Repeated natural modules use the same action on
every summand. The four-dimensional exceptional module is indecomposable,
with its actual commutator submodule identified with the natural SL₃(2)
representation, as in B.4.8(3).

No classification is asserted here. These definitions retain the action,
quotient, field and extension data needed by B.5.6(2)–(5).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.8,
printed p.91, and B.5.6, printed p.105.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
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

/-- The group-only list for each direct factor in B.5.6(3). Rank-two
linear groups use SL₂ in characteristic two; rank-three groups have odd
field degree, so their scalar centers are trivial as well. -/
inductive FactorModel (D : Type u) [Group D] : Prop
  | linearTwo (F : BinaryField)
      (equiv : D ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier)
  | symmetricFive (equiv : D ≃* Equiv.Perm (Fin 5))
  | linearThree (F : BinaryField) (odd_degree : Odd F.degree)
      (equiv : D ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier)

/-- The natural module possibilities for one factor, with field restrictions. -/
inductive FactorNatural : Prop
  | linearTwo (F : BinaryField) (natural : IsLinearNatural ρ F 2)
  | symmetricFive (natural : IsSymmetricNatural ρ 5)
  | linearThree (F : BinaryField) (odd_degree : Odd F.degree)
      (natural : IsLinearNatural ρ F 3)

/-- An internal product is tied to the original two inclusions. -/
structure InternalProduct (A B : Subgroup D) where
  equiv : (A × B) ≃* D
  apply_eq : ∀ a b, equiv (a, b) = (a : D) * (b : D)

/-- An FF witness excludes the trivial group allowed by B.5.3. -/
theorem nontrivial_of_ff (h : IsFFModule ρ) : Nontrivial D := by
  obtain ⟨A, hA⟩ := h
  have : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA.1.1
  exact Function.Injective.nontrivial A.subtype_injective

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
