module

public import Theory.AlgebraicGroup.Automorphisms.Basic
public import Theory.AlgebraicGroup.RootData.Chevalley

universe u

/-! GLS3, Chapter 1, Definition 1.15.1 and Theorem 1.15.2(a). -/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k]

/-- Isometries of the Dynkin diagram attached to the chosen fundamental system. -/
@[expose]
public def IsDiagramIsometry
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (ρ : Equiv.Perm D.Root) : Prop :=
  (∀ α, α ∈ D.simple ↔ ρ α ∈ D.simple) ∧
    ∀ α β, D.pairing (ρ α) (ρ β) = D.pairing α β

public def DiagramIsometryGroup
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) : Subgroup (Equiv.Perm D.Root) where
  carrier := {ρ | IsDiagramIsometry D ρ}
  mul_mem' := by
    rintro ρ σ ⟨hρs, hρp⟩ ⟨hσs, hσp⟩
    constructor
    · intro α
      simp only [Equiv.Perm.mul_apply]
      exact (hσs α).trans (hρs (σ α))
    · intro α β
      simp only [Equiv.Perm.mul_apply]
      rw [hρp, hσp]
  one_mem' := by
    constructor <;> simp
  inv_mem' := by
    rintro ρ ⟨hρs, hρp⟩
    constructor
    · intro α
      simpa using (hρs (ρ⁻¹ α)).symm
    · intro α β
      simpa using (hρp (ρ⁻¹ α) (ρ⁻¹ β)).symm

@[expose]
public def IsSignedFundamentalRoot
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (α : D.Root) : Prop :=
  α ∈ D.simple ∨ D.neg α ∈ D.simple

/-- The defining Chevalley-generator formula for `γ_ρ`. -/
@[expose]
public def IsGraphAutomorphism
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    (ρ : Equiv.Perm D.Root) (γ : Aut K) : Prop :=
  γ ∈ AutZero K ∧ IsDiagramIsometry D ρ ∧
    ∀ α, IsSignedFundamentalRoot D α → ∀ t, γ (C.x α t) = C.x (ρ α) t

/-- The graph automorphisms supplied by the chosen root and Chevalley data. -/
@[expose]
public def GammaZeroSet
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D) : Set (Aut K) :=
  {γ | ∃ ρ : Equiv.Perm D.Root, IsGraphAutomorphism D C ρ γ}

public def TrialityRootNormalClosure
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (γ : Aut K) (α : D.Root) :
    Subgroup (Variety.Point K) :=
  Subgroup.closure (⋃ n : ℤ, (γ ^ n) '' (D.rootSubgroup α : Set (Variety.Point K)))

/-- The point-group elements occurring in the formula defining a graph automorphism. -/
@[expose]
public def SignedFundamentalRootElementSet
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D) : Set (Variety.Point K) :=
  {x | ∃ α, IsSignedFundamentalRoot D α ∧ ∃ t, x = C.x α t}

/-- The explicit generation input missing from the current root-data API. -/
@[expose]
public def HasSignedFundamentalRootGeneration
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D) : Prop :=
  Subgroup.closure (SignedFundamentalRootElementSet D C) = ⊤

@[expose]
public def IsLongRoot
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (α : D.Root) : Prop :=
  ∃ β, |D.pairing β α| > |D.pairing α β|

@[expose]
public def IsShortRoot
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (α : D.Root) : Prop :=
  ∃ β, |D.pairing α β| > |D.pairing β α|

/-- The identity abstract automorphism realizes the identity diagram
isometry as a graph automorphism. -/
public lemma isGraphAutomorphism_one
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D) :
    IsGraphAutomorphism D C (1 : Equiv.Perm D.Root) (1 : Aut K) := by
  refine ⟨(AutZero K).one_mem, ?_, ?_⟩
  · constructor <;> simp
  · intro α _ t
    simp

/-- Two abstract automorphisms agreeing on the signed fundamental root
elements agree everywhere once those elements generate the point group. -/
public lemma graphAutomorphism_eq_of_signedFundamentalRootGeneration
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    (hgen : HasSignedFundamentalRootGeneration D C)
    (γ₁ γ₂ : Aut K)
    (hagree : ∀ α, IsSignedFundamentalRoot D α →
      ∀ t, γ₁ (C.x α t) = γ₂ (C.x α t)) :
    γ₁ = γ₂ := by
  have hhom : γ₁.toMonoidHom = γ₂.toMonoidHom :=
    MonoidHom.eq_of_eqOn_dense hgen (by
      rintro x ⟨α, hα, t, rfl⟩
      exact hagree α hα t)
  apply MulEquiv.ext
  intro x
  exact DFunLike.congr_fun hhom x

/-- Theorem 1.15.2(a), honest uniqueness core. The current API does not yet
prove that semisimplicity and raw root realization imply generation by the
signed fundamental root elements, so that generation statement is explicit. -/
public theorem graphAutomorphism_unique_of_signedFundamentalRootGeneration
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    (hgen : HasSignedFundamentalRootGeneration D C) :
    ∀ ρ : Equiv.Perm D.Root, IsDiagramIsometry D ρ →
      ∀ γ₁ γ₂ : Aut K,
        IsGraphAutomorphism D C ρ γ₁ →
        IsGraphAutomorphism D C ρ γ₂ → γ₁ = γ₂ := by
  intro ρ _ γ₁ γ₂ hγ₁ hγ₂
  apply graphAutomorphism_eq_of_signedFundamentalRootGeneration D C hgen
  intro α hα t
  rw [hγ₁.2.2 α hα t, hγ₂.2.2 α hα t]

end

end Theory.AlgebraicGroup
