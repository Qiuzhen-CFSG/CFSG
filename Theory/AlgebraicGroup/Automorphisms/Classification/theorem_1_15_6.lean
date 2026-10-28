module

public import Theory.AlgebraicGroup.Automorphisms.Classification.theorem_1_15_4

/-!
Version transport and the canonical data used for Steinberg endomorphisms.

GLS3 Theorem 1.15.6 compares algebraic automorphisms and Steinberg
endomorphisms across the universal, intermediate, and adjoint versions of a
simple algebraic group.  The definitions following it prepare Theorem 1.15.7.
In particular, `IsCanonicalSteinbergData` records the setup inherited from
GLS3 Theorem 1.15.4 and Definition 1.15.5: one reduced crystallographic root
system realized by `D`, its Dynkin classification, a Chevalley system for `C`
encoding the Chevalley relations, root-element generation, and the compatible
Frobenius and exceptional graph-field formulas.  Keeping these witnesses in a
single exposed contract ensures that every formula and classification refers
to the same chosen root and Chevalley data.
-/

set_option warningAsError false

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_1_15_6
    {Ku K Ka : Variety k} [AlgebraicGroup Ku] [AlgebraicGroup K] [AlgebraicGroup Ka]
    (u : AlgebraicGroup.Morphism Ku K) (a : AlgebraicGroup.Morphism K Ka)
    (hu : IsIsogeny u) (ha : IsIsogeny a)
    (hK : IsSimpleAlgebraicGroup K)
    (hKu : IsUniversalVersion Ku) (hKa : IsAdjointVersion Ka) :
    (∀ σ : Aut K, σ ∈ AutZero K →
      ∃! σu : Aut Ku,
        σu ∈ AutZero Ku ∧ AbstractAutomorphismsCommuteWith u σu σ) ∧
    (∀ σ : Aut K, σ ∈ AutZero K →
      ∃! σa : Aut Ka,
        σa ∈ AutZero Ka ∧ AbstractAutomorphismsCommuteWith a σ σa) ∧
    (∀ σ : Aut K, σ ∈ SteinbergAutomorphismSet K →
      ∃! σu : Aut Ku,
        σu ∈ SteinbergAutomorphismSet Ku ∧
          AbstractAutomorphismsCommuteWith u σu σ) ∧
    (∀ σ : Aut K, σ ∈ SteinbergAutomorphismSet K →
      ∃! σa : Aut Ka,
        σa ∈ SteinbergAutomorphismSet Ka ∧
          AbstractAutomorphismsCommuteWith a σ σa) ∧
    (∃ lift : AutZero K →* AutZero Ku,
      Function.Injective lift ∧
        ∀ σ : AutZero K,
          AbstractAutomorphismsCommuteWith u (lift σ).1 σ.1) ∧
    (∃ descend : AutZero K →* AutZero Ka,
      Function.Injective descend ∧
        ∀ σ : AutZero K,
          AbstractAutomorphismsCommuteWith a σ.1 (descend σ).1) ∧
    (∃ lift : { σ : Aut K // σ ∈ AutOneSet K } →
        { σ : Aut Ku // σ ∈ AutOneSet Ku },
      Function.Injective lift ∧
        ∀ σ, AbstractAutomorphismsCommuteWith u (lift σ).1 σ.1) ∧
    (∃ descend : { σ : Aut K // σ ∈ AutOneSet K } →
        { σ : Aut Ka // σ ∈ AutOneSet Ka },
      Function.Injective descend ∧
        ∀ σ, AbstractAutomorphismsCommuteWith a σ.1 (descend σ).1) ∧
    (∃ e : AutZero Ku ≃* AutZero Ka,
      ∀ σ : AutZero Ku, ∀ x,
        a.onPoints (u.onPoints (σ.1 x)) =
          (e σ).1 (a.onPoints (u.onPoints x))) ∧
    (∃ e : { σ : Aut Ku // σ ∈ AutOneSet Ku } ≃
        { σ : Aut Ka // σ ∈ AutOneSet Ka },
      ∀ σ, ∀ x,
        a.onPoints (u.onPoints (σ.1 x)) =
          (e σ).1 (a.onPoints (u.onPoints x))) := by sorry

public def evenPowers {α : Type*} [Group α] (s : α) : Set α :=
  Set.range (fun n : ℤ => s ^ (2 * n))

public def IsInfiniteOrderAut
    {K : Variety k} [AlgebraicGroup K] (s : Aut K) : Prop :=
  ∀ n : ℤ, n ≠ 0 → s ^ n ≠ 1

public def IsGraphFieldGeneratorFormula
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    (F : FrobeniusScalarSystem (k := k) (ringChar k)) (ψ : Aut K) : Prop :=
  ∃ ρ : Equiv.Perm D.Root,
    (∀ α, α ∈ D.simple ↔ ρ α ∈ D.simple) ∧
      (∀ α, IsLongRoot D α ↔ IsShortRoot D (ρ α)) ∧
      (∀ α, IsShortRoot D α ↔ IsLongRoot D (ρ α)) ∧
        (∀ α β,
          D.pairing (ρ α) (ρ β) * D.pairing (ρ β) (ρ α) =
            D.pairing α β * D.pairing β α) ∧
          ((∀ α, IsLongRoot D α → ∀ t,
              ψ (C.x α t) = C.x (ρ α) t) ∧
            ∀ α, IsShortRoot D α → ∀ t,
              ψ (C.x α t) = C.x (ρ α) (F.scalar 1 t))

@[expose]
public def IsCanonicalSteinbergData
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    (classification : RootClassification) (φ : ℤ → Aut K) (ψ : Aut K) : Prop :=
  Nonempty (SteinbergChevalleyRootSystem D C) ∧
    D.HasDynkinClassificationForSteinberg classification ∧
    ∃ F : FrobeniusScalarSystem (k := k) (ringChar k), ∃ f : Aut K,
      ∃ fAlg : AlgebraicEndomorphism K,
        IsAlgebraicRealization f fAlg ∧
          IsAlgebraicSteinbergEndomorphism fAlg ∧
          IsFrobeniusGeneratorFormula D C F 1 f ∧
          (∀ n : ℤ, φ n = f ^ n) ∧ IsInfiniteOrderAut f ∧
          (IsExceptionalSteinbergType classification (ringChar k) →
            ∃ ψAlg : AlgebraicEndomorphism K,
              IsAlgebraicRealization ψ ψAlg ∧
                IsAlgebraicSteinbergEndomorphism ψAlg ∧ ψ ^ 2 = φ 1 ∧
                  IsGraphFieldGeneratorFormula D C F ψ ∧ IsInfiniteOrderAut ψ)

end Theory.AlgebraicGroup
