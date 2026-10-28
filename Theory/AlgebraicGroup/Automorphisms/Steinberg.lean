module

public import Theory.AlgebraicGroup.Automorphisms.Basic
public import Theory.AlgebraicGroup.RootData.Chevalley

universe u

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k]

@[expose]
public def IsAlgebraicSteinbergEndomorphism
    {K : Variety k} [AlgebraicGroup K] (σ : AlgebraicEndomorphism K) : Prop :=
  Function.Surjective σ.onPoints ∧
    Finite {x : Variety.Point K | σ.onPoints x = x}

public structure FrobeniusScalarSystem (r : ℕ) where
  scalar : ℤ → k ≃+* k
  zero : scalar 0 = RingEquiv.refl k
  add : ∀ a b x, scalar (a + b) x = scalar a (scalar b x)
  nonnegative : ∀ a : ℕ, ∀ x, scalar a x = x ^ (r ^ a)

/-- The full set of root elements attached to raw Chevalley data. -/
@[expose]
public def ChevalleyRootElementSet
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D) : Set (Variety.Point K) :=
  Set.range fun z : D.Root × k => C.x z.1 z.2

/-- The explicit generation input missing from raw `ChevalleyData`. -/
@[expose]
public def HasChevalleyRootGeneration
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D) : Prop :=
  Subgroup.closure (ChevalleyRootElementSet D C) = ⊤

/-- The root-element formula for a supplied integral Frobenius automorphism. -/
@[expose]
public def IsFrobeniusGeneratorFormula
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    (F : FrobeniusScalarSystem (k := k) (ringChar k))
    (a : ℤ) (φ : Aut K) : Prop :=
  ∀ α t, φ (C.x α t) = C.x α (F.scalar a t)

/-- Abstract automorphisms agreeing on a generating family of Chevalley root
elements agree everywhere. -/
public lemma automorphism_eq_of_chevalleyRootGeneration
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    (hgen : HasChevalleyRootGeneration D C)
    {φ ψ : Aut K}
    (h : ∀ α t, φ (C.x α t) = ψ (C.x α t)) :
    φ = ψ := by
  ext x
  have hx : x ∈ Subgroup.closure (ChevalleyRootElementSet D C) := by
    rw [hgen]
    exact Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      change x ∈ Set.range (fun z : D.Root × k => C.x z.1 z.2) at hx
      obtain ⟨⟨α, t⟩, rfl⟩ := hx
      exact h α t
  | one => simp
  | mul x y _ _ hx hy => simp [hx, hy]
  | inv x _ hx => simp [hx]

/-- The abstract automorphisms realized by Steinberg endomorphisms. -/
@[expose]
public def SteinbergAutomorphismSet
    (K : Variety k) [AlgebraicGroup K] : Set (Aut K) :=
  {σ | ∃ f : AlgebraicEndomorphism K,
    IsAlgebraicRealization σ f ∧ IsAlgebraicSteinbergEndomorphism f}

end

end Theory.AlgebraicGroup
