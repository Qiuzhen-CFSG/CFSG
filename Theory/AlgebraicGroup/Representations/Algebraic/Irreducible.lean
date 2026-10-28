module

public import Theory.AlgebraicGroup.Representations.Operations

universe u v w

/-!
Irreducible algebraic representations and composition factors.

The orbit-span criterion below packages the elementary irreducibility argument
used by relative-root representations: a nonzero invariant submodule detects a
distinguished vector, and the full group orbit of that vector spans the module.
It is an abstract linear-algebra reduction for the GLS3 relative-root route and
does not depend on the still-unproved numbered irreducibility theorem.
-/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public def IsAlgebraicallyIrreducibleRepresentation
    {K : Variety k} [AlgebraicGroup K] {V : Type v}
    [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) : Prop :=
  ∀ W : Submodule k V, IsInvariantSubmodule ρ W → W = ⊥ ∨ W = ⊤

@[expose]
public def IsCyclicRepresentation
    {K : Variety k} [AlgebraicGroup K] {V : Type v}
    [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) (v : V) : Prop :=
  ∀ W : Submodule k V, IsInvariantSubmodule ρ W → v ∈ W → W = ⊤

omit [IsAlgClosed k] in
/-- A representation is irreducible when every nonzero invariant submodule
detects an eligible generator whose full group orbit spans the module. -/
public theorem isAlgebraicallyIrreducibleRepresentation_of_generator_detection_of_orbit_span
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V)
    {Z : Type w} (generator : Z → V) (eligible : Z → Prop)
    (hdetect : ∀ W : Submodule k V,
      IsInvariantSubmodule ρ W → W ≠ ⊥ →
        ∃ z, eligible z ∧ generator z ∈ W)
    (horbit : ∀ z, eligible z →
      Submodule.span k (Set.range fun g : Variety.Point K =>
        (ρ.action g).1 (generator z)) = ⊤) :
    IsAlgebraicallyIrreducibleRepresentation ρ := by
  intro W hW
  by_cases hWbot : W = ⊥
  · exact Or.inl hWbot
  · right
    obtain ⟨z, hz, hzW⟩ := hdetect W hW hWbot
    apply top_unique
    rw [← horbit z hz]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact hW g _ hzW

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public def IsIrreducibleRepresentation
    {K : Variety k} [AlgebraicGroup K] {V : Type v}
    [AddCommGroup V] [Module k V]
    (ρ : RationalRepresentation K V) : Prop :=
  IsRationalRepresentation ρ ∧
    ∀ W : Submodule k V, IsInvariantSubmodule ρ W → W = ⊥ ∨ W = ⊤

@[expose]
public def AreEquivalentRepresentations
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : RationalRepresentation K V) (σ : RationalRepresentation K W) : Prop :=
  ∃ e : V ≃ₗ[k] W, Intertwines ρ σ e.toLinearMap

@[expose]
public def IsRepresentationSectionOf
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : RationalRepresentation K V) (σ : RationalRepresentation K W) : Prop :=
  ∃ A : Type (max v w), ∃ _ : AddCommGroup A, ∃ _ : Module k A,
    ∃ τ : RationalRepresentation K A,
    ∃ inclusion : A →ₗ[k] V, ∃ quotient : A →ₗ[k] W,
      Function.Injective inclusion ∧ Function.Surjective quotient ∧
      Intertwines τ ρ inclusion ∧ Intertwines τ σ quotient

@[expose]
public def IsCompositionFactorOf
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : RationalRepresentation K V) (σ : RationalRepresentation K W) : Prop :=
  IsIrreducibleRepresentation σ ∧ IsRepresentationSectionOf ρ σ

end

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The rational contragredient of a finite-dimensional irreducible
representation is irreducible. -/
public theorem dualRepresentation_isIrreducible
    {K : Variety k} [AlgebraicGroup K]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation K V)
    (τ : RationalRepresentation K (Module.Dual k V))
    (hτ : IsDualRepresentation ρ τ) (hirr : IsIrreducibleRepresentation ρ)
    (hτRational : IsRationalRepresentation τ) : IsIrreducibleRepresentation τ := by
  refine ⟨hτRational, ?_⟩
  intro W hW
  have hCoInvariant : IsInvariantSubmodule ρ W.dualCoannihilator := by
    intro g x hx
    rw [Submodule.mem_dualCoannihilator] at hx ⊢
    intro f hf
    have hInv : (τ.action g⁻¹).1 f ∈ W := hW g⁻¹ f hf
    have hZero := hx ((τ.action g⁻¹).1 f) hInv
    rw [hτ] at hZero
    simpa using hZero
  rcases hirr.2 W.dualCoannihilator hCoInvariant with hbot | htop
  · right
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hbot]
    simp
  · left
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), htop]
    simp

end

end Theory.AlgebraicGroup
