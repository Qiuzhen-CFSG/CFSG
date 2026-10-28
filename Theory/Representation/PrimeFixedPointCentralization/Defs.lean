module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Algebra.Field.ZMod
public import Theory.ElementaryAbelian.Extraspecial

/-!
# Interfaces for the minimal-action reduction in the prime fixed-vector theorem

Aschbacher, *Finite Group Theory*, second edition, 36.2 (printed p.194),
reduces a faithful action of a prime-order group on a group of different
prime-power order to a faithful irreducible module and an action centralizing
every proper invariant subgroup. The two statements below separate that
reduction from the abelian and extraspecial calculations. They are proof
obligations, not asserted theorems.

The scalar field is binary, as needed by the odd-order application. All
actions and faithfulness hypotheses concern actual homomorphisms.
-/

universe u

namespace Representation.PrimeFixedPointCentralization

/-- Every proper invariant subgroup is centralized by the acting group. -/
@[expose] public def IsMinimalAction {P A : Type*} [Group P] [Group A]
    (φ : A →* MulAut P) : Prop :=
  ∀ Q : Subgroup P, (∀ a : A, ∀ z ∈ Q, φ a z ∈ Q) → Q ≠ ⊤ →
    ∀ a : A, ∀ z ∈ Q, φ a z = z

/-- The two group configurations in the minimal-action argument. Existence
of this alternative is a separate group-theoretic obligation; this definition
includes neither a representation nor its desired fixed vector. -/
@[expose] public def HasMinimalActionStructure {P A : Type*} [Group P] [Group A]
    (q : ℕ) (φ : A →* MulAut P) : Prop :=
  (IsMulCommutative P ∧
    ∀ a : A, a ≠ 1 → ∀ z : P, φ a z = z → z = 1) ∨
  ∃ n : ℕ, IsExtraspecial q P ∧ Nat.card P = q ^ (2 * n + 1) ∧
    ∀ a : A, a ≠ 1 → {z | φ a z = z} = (Subgroup.center P : Set P)

/-- The representation-theoretic obligation for minimal faithful actions.
The extra minimality and irreducibility premises must be removed before using
this statement for a general linear subgroup. -/
@[expose] public def MinimalFixedVectorStatement (q r : ℕ) : Prop :=
  ∀ (P A W : Type u) [Group P] [Finite P] [Group A] [Finite A]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W],
    IsPGroup q P → Nat.card A = r →
    ∀ φ : A →* MulAut P, Function.Injective φ → IsMinimalAction φ →
    ∀ ρ : Representation (ZMod 2) (SemidirectProduct P A φ) W,
    ρ.IsIrreducible → Function.Injective ρ →
    ∃ v : W, v ≠ 0 ∧ ∀ a : A, ρ (SemidirectProduct.inr a) v = v

/-- The full semidirect-product fixed-vector obligation, with no minimality
or irreducibility premise. -/
@[expose] public def PrimeActionFixedVectorStatement (q r : ℕ) : Prop :=
  ∀ (P A W : Type u) [Group P] [Finite P] [Group A] [Finite A]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W],
    IsPGroup q P → Nat.card A = r →
    ∀ φ : A →* MulAut P, Function.Injective φ →
    ∀ ρ : Representation (ZMod 2) (SemidirectProduct P A φ) W,
    Function.Injective ρ →
    ∃ v : W, v ≠ 0 ∧ ∀ a : A, ρ (SemidirectProduct.inr a) v = v

end Representation.PrimeFixedPointCentralization
