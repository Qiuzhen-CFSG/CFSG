module

public import Theory.AlgebraicGroup.Automorphisms.GraphCore
public import Theory.AlgebraicGroup.Automorphisms.SteinbergCore
public import Theory.AlgebraicGroup.RootSystems.Defs

universe u

/-!
Set-level forms of GLS3 Definition 1.15.5.

The maintained root-group data intentionally does not store a Dynkin
classification tag.  The classification and the characteristic are therefore
explicit inputs to the exceptional branch.  All assertions in this file are
definitional consequences of those set-level choices; subgroup, cyclicity,
and `Aut₀ · Φ · Γ` decomposition statements require the separate geometric
and endomorphism-construction results listed in `.temp/absence.md`.
-/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k]

/-- The three exceptional Steinberg types, with their required
characteristics. -/
@[expose]
public def IsExceptionalSteinbergType
    (classification : RootClassification) (p : ℕ) : Prop :=
  (classification.kind = .B ∧ classification.rank = 2 ∧ p = 2) ∨
  (classification.kind = .F4 ∧ classification.rank = 4 ∧ p = 2) ∨
  (classification.kind = .G2 ∧ classification.rank = 2 ∧ p = 3)

/-- The integral powers in an explicitly supplied Frobenius family. -/
@[expose]
public def Phi {K : Variety k} [AlgebraicGroup K]
    (φ : ℤ → Aut K) : Set (Aut K) :=
  Set.range φ

/-- The positive part of an explicitly supplied Frobenius family. -/
@[expose]
public def PhiPos {K : Variety k} [AlgebraicGroup K]
    (φ : ℤ → Aut K) : Set (Aut K) :=
  {σ | ∃ a : ℤ, 0 < a ∧ σ = φ a}

/-- The set `S` from Definition 1.15.5 before any subgroup assertion. -/
@[expose]
public def S
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (_D : RootGroupData K T) (classification : RootClassification)
    (φ : ℤ → Aut K) (ψ : Aut K) : Set (Aut K) := by
  classical
  exact if IsExceptionalSteinbergType classification (ringChar k) then
    (Subgroup.zpowers ψ : Set (Aut K)) else Phi φ

/-- The positive part of `S`. -/
@[expose]
public def SPos
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (_D : RootGroupData K T) (classification : RootClassification)
    (φ : ℤ → Aut K) (ψ : Aut K) : Set (Aut K) := by
  classical
  exact if IsExceptionalSteinbergType classification (ringChar k) then
    {σ | ∃ a : ℤ, 0 < a ∧ σ = ψ ^ a} else PhiPos φ

/-- The graph set from Definition 1.15.5. -/
@[expose]
public def Gamma
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    (classification : RootClassification) (ψ : Aut K) : Set (Aut K) := by
  classical
  exact if IsExceptionalSteinbergType classification (ringChar k) then
    {1, ψ} else GammaZeroSet D C

/-- The set-level identities and positive-part inclusions that follow from
Definition 1.15.5 alone. -/
public theorem steinbergSets_core
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    (classification : RootClassification) (φ : ℤ → Aut K) (ψ : Aut K) :
    Phi φ = Set.range φ ∧
    PhiPos φ = {σ | ∃ a : ℤ, 0 < a ∧ σ = φ a} ∧
    (IsExceptionalSteinbergType classification (ringChar k) →
      S D classification φ ψ = (Subgroup.zpowers ψ : Set (Aut K)) ∧
      SPos D classification φ ψ = {σ | ∃ a : ℤ, 0 < a ∧ σ = ψ ^ a}) ∧
    (¬ IsExceptionalSteinbergType classification (ringChar k) →
      S D classification φ ψ = Phi φ ∧
      SPos D classification φ ψ = PhiPos φ ∧
      Gamma D C classification ψ = GammaZeroSet D C) ∧
    SPos D classification φ ψ ⊆ S D classification φ ψ ∧
    (IsExceptionalSteinbergType classification (ringChar k) →
      Gamma D C classification ψ = {1, ψ}) := by
  have hPhiPos : PhiPos φ ⊆ Phi φ := by
    rintro σ ⟨a, _, rfl⟩
    exact ⟨a, rfl⟩
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro hexceptional
    exact ⟨by rw [S]; simp [hexceptional], by rw [SPos]; simp [hexceptional]⟩
  · intro hordinary
    refine ⟨by rw [S]; simp [hordinary], by rw [SPos]; simp [hordinary], ?_⟩
    rw [Gamma]
    simp [hordinary]
  · intro σ hσ
    by_cases hexceptional : IsExceptionalSteinbergType classification (ringChar k)
    · rw [S, if_pos hexceptional]
      rw [SPos, if_pos hexceptional] at hσ
      obtain ⟨a, _, rfl⟩ := hσ
      exact ⟨a, rfl⟩
    · rw [S, if_neg hexceptional]
      rw [SPos, if_neg hexceptional] at hσ
      exact hPhiPos hσ
  · intro hexceptional
    rw [Gamma]
    simp [hexceptional]

end

end Theory.AlgebraicGroup
