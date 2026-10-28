module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot

/-!
# Graph automorphism classification interfaces

This module contains the root-system realization and classification interfaces
used by GLS3 Theorem 1.15.2.  Keeping these definitions below the theorem module
makes the theorem an isolated proof target while preserving the original public
API and source order.
-/

set_option warningAsError false

universe u v w

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public structure GraphChevalleyRootSystem
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D) where
  isMaximalTorus : IsMaximalTorus T
  realizesRootGroups : D.IsRealization
  ι : Type u
  E : Type u
  E' : Type u
  [finiteRoot : Finite ι]
  [addCommGroupWeight : AddCommGroup E]
  [weightSpace : Module ℝ E]
  [addCommGroupCoweight : AddCommGroup E']
  [coweightSpace : Module ℝ E']
  pairing : RootPairing ι ℝ E E'
  [isRootSystem : pairing.IsRootSystem]
  [isCrystallographic : pairing.IsCrystallographic]
  [isReduced : pairing.IsReduced]
  rootEquiv : D.Root ≃ ι
  base : pairing.Base
  realizesRoots : IsRootSystemRealization D pairing rootEquiv base
  isChevalleySystem : IsChevalleySystem D C pairing rootEquiv base
  rootGeneration : HasSignedFundamentalRootGeneration D C

attribute [instance] GraphChevalleyRootSystem.finiteRoot
  GraphChevalleyRootSystem.addCommGroupWeight GraphChevalleyRootSystem.weightSpace
  GraphChevalleyRootSystem.addCommGroupCoweight GraphChevalleyRootSystem.coweightSpace
  GraphChevalleyRootSystem.isRootSystem GraphChevalleyRootSystem.isCrystallographic
  GraphChevalleyRootSystem.isReduced

public def RootGroupData.HasDynkinClassification
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (classification : RootClassification) : Prop :=
  Nonempty {e : D.simple ≃ Fin classification.rank //
    ∀ i j, D.pairing i.1 j.1 = dynkinCartanEntry classification (e i) (e j)}

public def abstractAutomorphismFixedPoints
    {K : Variety k} [AlgebraicGroup K] (γ : Aut K) :
    Subgroup (Variety.Point K) where
  carrier := {x | γ x = x}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change γ (x * y) = x * y
    rw [map_mul, hx, hy]
  inv_mem' := by
    intro x hx
    change γ x⁻¹ = x⁻¹
    rw [map_inv, hx]

public def DiagramIsometryExtendsToWeightLattice
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (ρ : Equiv.Perm D.Root) : Prop :=
  ∃ e : TorusWeight T ≃* TorusWeight T,
    ∀ α, e (D.rootWeight α) = D.rootWeight (ρ α)

public def IsGraphFixedPointClassification
    (source : RootClassification) (p order : ℕ)
    (target : RootClassification) : Prop :=
  (source.kind = .A ∧ 1 < source.rank ∧ order = 2 ∧
      ((Even source.rank ∧ Odd p ∧ target = { kind := .B, rank := source.rank / 2 }) ∨
        ((¬ Even source.rank ∨ ¬ Odd p) ∧
          target = { kind := .C, rank := (source.rank + 1) / 2 }))) ∨
  (source.kind = .D ∧ 4 < source.rank ∧ order = 2 ∧
      target = { kind := .B, rank := source.rank - 1 }) ∨
  (source.kind = .D ∧ source.rank = 4 ∧ order = 2 ∧
      target = { kind := .B, rank := 3 }) ∨
  (source.kind = .D ∧ source.rank = 4 ∧ order = 3 ∧
      target = { kind := .G2, rank := 2 }) ∨
  (source.kind = .E6 ∧ source.rank = 6 ∧ order = 2 ∧
      target = { kind := .F4, rank := 4 })

public structure GraphAutomorphismClassification
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (hK : IsSemisimpleAlgebraicGroup K)
    (D : RootGroupData K T) (C : ChevalleyData K D)
    (setup : GraphChevalleyRootSystem D C) where
  unique : ∀ ρ, IsDiagramIsometry D ρ →
    ∀ γ₁ γ₂, IsGraphAutomorphism D C ρ γ₁ →
      IsGraphAutomorphism D C ρ γ₂ → γ₁ = γ₂
  weight_lattice_exists : ∀ ρ, IsDiagramIsometry D ρ →
    DiagramIsometryExtendsToWeightLattice D ρ →
      ∃! γ : Aut K, IsGraphAutomorphism D C ρ γ
  extreme_exists : ∀ (hExtreme : IsUniversalVersion K ∨ IsAdjointVersion K)
    ρ, IsDiagramIsometry D ρ →
      ∃! γ : Aut K, IsGraphAutomorphism D C ρ γ
  subgroup_exists : ∃ Γ₀ : Subgroup (Aut K),
    (Γ₀ : Set (Aut K)) = GammaZeroSet D C
  diagram_embedding : ∀ Γ₀ : Subgroup (Aut K),
    (Γ₀ : Set (Aut K)) = GammaZeroSet D C →
      ∃ f : Γ₀ →* DiagramIsometryGroup D, Function.Injective f
  diagram_isomorphism : ∀ (hExtreme : IsUniversalVersion K ∨ IsAdjointVersion K)
    (Γ₀ : Subgroup (Aut K)),
    (Γ₀ : Set (Aut K)) = GammaZeroSet D C →
      Nonempty (Γ₀ ≃* DiagramIsometryGroup D)
  autZero_decomposition : ∀ Γ₀ : Subgroup (Aut K),
    (Γ₀ : Set (Aut K)) = GammaZeroSet D C →
      (AutZero K : Set (Aut K)) = setMul (Inn K : Set (Aut K)) Γ₀
  inner_intersection : ∀ Γ₀ : Subgroup (Aut K),
    (Γ₀ : Set (Aut K)) = GammaZeroSet D C → Inn K ⊓ Γ₀ = ⊥
  universal_center_inversion : ∀ (hUniversal : IsUniversalVersion K)
    (classification : RootClassification), D.HasDynkinClassification classification →
    ((classification.kind = .A ∧ 1 < classification.rank) ∨
      (classification.kind = .D ∧ Odd classification.rank) ∨
      classification.kind = .E6) →
    ∀ Γ₀ : Subgroup (Aut K),
      (Γ₀ : Set (Aut K)) = GammaZeroSet D C →
      ∀ γ : Aut K, γ ∈ Γ₀ → γ ≠ 1 →
        ∀ z, z ∈ Subgroup.center (Variety.Point K) → γ z = z⁻¹
  universal_center_complement_card_two :
    ∀ (hUniversal : IsUniversalVersion K)
      (classification : RootClassification), D.HasDynkinClassification classification →
      ((classification.kind = .A ∧ 1 < classification.rank) ∨
        (classification.kind = .D ∧ Odd classification.rank) ∨
        classification.kind = .E6) →
      ∀ Γ₀ : Subgroup (Aut K),
        (Γ₀ : Set (Aut K)) = GammaZeroSet D C → Nat.card Γ₀ = 2
  evenD_center_faithful :
    ∀ (hUniversal : IsUniversalVersion K)
      (classification : RootClassification), D.HasDynkinClassification classification →
      (classification.kind = .D ∧ Even classification.rank ∧ Odd (ringChar k)) →
      ∀ Γ₀ : Subgroup (Aut K),
        (Γ₀ : Set (Aut K)) = GammaZeroSet D C →
        ∀ γ δ : Aut K, γ ∈ Γ₀ → δ ∈ Γ₀ →
          (∀ z, z ∈ Subgroup.center (Variety.Point K) → γ z = δ z) → γ = δ
  fixedPoint_closed : ∀ ρ γ, IsGraphAutomorphism D C ρ γ →
    ∃ L : ClosedSubgroup K, L.toSubgroup = abstractAutomorphismFixedPoints γ
  fixedPoint_simple : ∀ ρ γ, IsGraphAutomorphism D C ρ γ → ρ ≠ 1 →
    ∀ L : ClosedSubgroup K, L.toSubgroup = abstractAutomorphismFixedPoints γ →
      IsSimpleAlgebraicGroup L.carrierVariety
  fixedPoint_type : ∀ (source : RootClassification) (ρ : Equiv.Perm D.Root)
      (γ : Aut K), IsGraphAutomorphism D C ρ γ → ρ ≠ 1 →
    ∀ L : ClosedSubgroup K, L.toSubgroup = abstractAutomorphismFixedPoints γ →
      letI := L.carrierAlgebraicGroup
      D.HasDynkinClassification source →
        ∃ (TL : ClosedSubgroup L.carrierVariety)
          (DL : RootGroupData L.carrierVariety TL) (target : RootClassification),
          RootGroupData.HasDynkinClassification DL target ∧
            IsGraphFixedPointClassification source (ringChar k) (orderOf ρ) target
  triality_refinement :
    ∀ (hClass : D.HasDynkinClassification { kind := .D, rank := 4 })
      (ρ : Equiv.Perm D.Root) (γ : Aut K),
      IsGraphAutomorphism D C ρ γ → orderOf ρ = 3 →
      ∃ τRoot : Equiv.Perm D.Root, ∃ τ : Aut K,
        IsGraphAutomorphism D C τRoot τ ∧ orderOf τRoot = 2 ∧
          τ * γ * τ⁻¹ = γ⁻¹ ∧
          abstractAutomorphismFixedPoints γ ≤
            abstractAutomorphismFixedPoints τ

end Theory.AlgebraicGroup
