module

public import Theory.Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OperatorModels
public import Theory.Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose
public import Theory.Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.SmallFieldTransvection

/-!
# Assembly of the concrete adjoint fixed-space estimates

The independent matrix calculations give three equations for a transpose
actor and four for a transvection actor. Exact Schur-field transport gives
`3s` in general and eight at `s = 2`. The elementary actor's common fixed
space is used throughout; cubicity and an offender inequality are unnecessary.

The outer-involution normal form and scalar rigidity identify the actual outer
operator with transpose. At the small-field endpoint, the outer two-rank bound
supplies a nonidentity inner actor, whose natural coordinates give the required
transvection. Together these prove `AdjointFixedSpaceBounds` from the genuine
adjoint Schur model, for arbitrary Hermitian forms and central kernels. Selecting
that model from an outer cubic actor remains a separate representation theorem.

Source: Guralnick--Malle, Classification of 2F-modules II,
Proposition 4.11, internal pp.31--32.
-/

public section
open BenderSuzuki.MatrixGroups Representation Representation.BinaryOffender

namespace Representation.SU3.CubicDegree.SchurOuter
open AdjointBounds
variable {F V : Type*} [Field F] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (J : HermitianForm 3 F)
  (σ : Representation (ZMod 2) J.specialSubgroup V) [σ.IsIrreducible]

/-- Conditional assembly from the actual operator realizations. Their
construction remains separate; neither is implied by this theorem. -/
theorem adjointFixedSpaceBounds_of_operator_realizations {s : ℕ}
    (ho : OuterTransposeRealization J σ s)
    (hi : s = 2 → SmallFieldTransvectionRealization J σ) :
    AdjointFixedSpaceBounds J σ s := by
  intro hm A hA hl t ht hout
  constructor
  · exact three_mul_le_fixedCodim σ A hl hm.fieldDegree ⟨t, ht⟩
      (ho hm A hA hl t ht hout)
  · rintro rfl htwo
    obtain ⟨a, ha⟩ := hi rfl hm A hA hl htwo
    exact four_mul_le_fixedCodim σ A hl hm.fieldDegree a ha

/-- The actual adjoint Schur model has common fixed codimension at least `3s`
for a Schur-linear elementary two-subgroup containing an outer actor. At `s = 2`,
rank at least two gives the stronger bound eight. No cubicity or offender
inequality is assumed. -/
theorem adjointFixedSpaceBounds [Finite F] {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (hk : σ.ker ≤ Subgroup.center J.specialSubgroup) :
    AdjointFixedSpaceBounds J σ s := by
  apply adjointFixedSpaceBounds_of_operator_realizations J σ
    (OuterTranspose.outerTransposeRealization J σ hs hcard hconj hk)
  rintro rfl
  exact smallFieldTransvectionRealization J hcard hconj σ hk

end Representation.SU3.CubicDegree.SchurOuter
