module

public import Theory.Representation.CyclicRootBrauerCharacter
public import Theory.Character.ConjClassFunction
public import Mathlib.Algebra.Module.Projective

/-!
# Module-valued output of a real cyclic-defect line

The vertices label ordinary characters and the edges are actual simple
representations. Incidence describes their lifted characters. Each adjacent
ordinary sum is required to be afforded, on regular elements, by an actual
projective module. Thus this interface retains the projectivity needed for
Brauer reciprocity; it is not just a numerical decomposition matrix.

There is no existence theorem or instance here. The intended producer is
cyclic-defect theory: Feit, *The Representation Theory of Finite Groups*,
VII.2.13--15, VII.6.8, VII.9.2. The consumer is the principal eleven-block
construction for the source group in Janko (1966).
-/

public section
noncomputable section
open scoped BigOperators

namespace Representation.CyclicDefect

/-- Incidence of the path with `n` edges and `n+1` vertices. -/
@[expose] def incidence {A : Type*} [AddCommMonoid A] {n : ℕ}
    (v : Fin n → A) (i : Fin (n + 1)) : A :=
  ∑ k, if i = k.castSucc ∨ i = k.succ then v k else 0

/-- An actual projective representation affording a specified regular character. -/
structure ProjectiveCharacterLift {K : Type*} [Field K] {G : Type*} [Group G]
    (p : ℕ) {m : ℕ} (L : CyclicRootLift K m) (χ : G → ℂ) where
  degree : ℕ
  rep : Representation K G (Fin degree → K)
  projective : Module.Projective (MonoidAlgebra K G) rep.asModule
  character_eq : ∀ g, ¬ p ∣ orderOf g → L.value rep g = χ g

/-- The regular scalar product uses the group order as denominator. The
equivalent class-sum convention uses reciprocal centralizer orders. -/
@[expose] def regularPairing {G : Type*} [Group G] [Finite G]
    (p : ℕ) (φ ψ : G → ℂ) : ℂ := by
  classical
  letI := Fintype.ofFinite G
  exact (Nat.card G : ℂ)⁻¹ * ∑ g : G, if ¬ p ∣ orderOf g then φ g * star (ψ g) else 0

/-- A complete line for one ordinary block, including its actual simple and
projective modules. Existence is a separate cyclic-defect theorem. -/
structure RealLine {K : Type*} [Field K] {G : Type*} [Group G] [Finite G]
    {I : Type*} [Fintype I] (χ : I → ConjClassFunction G) (block : Finset I)
    (principal : I) (p : ℕ) {m : ℕ} (n : ℕ) (L : CyclicRootLift K m) where
  row : Fin (n + 1) → I
  row_injective : Function.Injective row
  row_mem : ∀ i, row i ∈ block
  row_complete : ∀ i ∈ block, ∃ j, row j = i
  first_row : row 0 = principal
  degree : Fin n → ℕ
  rep : ∀ i, Representation K G (Fin (degree i) → K)
  irreducible : ∀ i, Representation.IsIrreducible (rep i)
  inequivalent : Pairwise fun i j => IsEmpty ((rep i).Equiv (rep j))
  decomposition : ∀ g, ¬ p ∣ orderOf g → ∀ i,
    χ (row i) (ConjClasses.mk g) = incidence (fun j => L.value (rep j) g) i
  projective : ∀ k : Fin n, ProjectiveCharacterLift p L
    (fun g => χ (row k.castSucc) (ConjClasses.mk g) + χ (row k.succ) (ConjClasses.mk g))

end Representation.CyclicDefect
