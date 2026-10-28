module

public import Theory.Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.MatrixEquations
public import Theory.Representation.SU3.CubicDegree.SchurOuter.Models
public import Theory.Representation.SU3.CubicDegree.SchurOuter.Literal

/-!
# Literal operator realizations for the adjoint bounds

The matrix equations give binary common fixed codimension at least `3s`
for a transpose actor and at least `4s` for a transvection actor, by the
proved exact Schur-field dimension transport.

The two realization predicates specify the remaining identifications on
these actual operators. They are mathematical obligations, not proved
classification assertions. The outer identification and the rank-two
small-field inner actor can be constructed independently. The owning
AdjointBounds assembly must discharge both.

Source: Guralnick--Malle, Classification of 2F-modules II,
Proposition 4.11, internal pp.31--32.
-/

public section

open BenderSuzuki.MatrixGroups Representation Representation.BinaryOffender
open Representation.FrobeniusTensor
namespace Representation.SU3.CubicDegree.SchurOuter.AdjointBounds
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (σ : Representation (ZMod 2) G V) [σ.IsIrreducible]
  (A : Subgroup (linearNormalizer σ))
  (hl : ∀ t ∈ A, SchurNormalizer.IsSchurLinear σ t)

/-- The absolute transpose equations give the binary common fixed-space bound. -/
theorem three_mul_le_fixedCodim {s : ℕ}
    (hd : Module.finrank (ZMod 2) (SchurField σ) = s) (a : A)
    (ha : IsTransposeOperator (absoluteActorRepresentation σ A hl a)) :
    3 * s ≤ fixedCodim (normalizerRepresentation σ) A := by
  rw [fixedCodim_eq_schur_mul σ A hl, hd]
  simpa only [Nat.mul_comm s 3] using
    Nat.mul_le_mul_left s (three_le_fixedCodim_of_transpose
      (absoluteActorRepresentation σ A hl) a ha)

/-- One absolute transvection suffices; the other actors can only reduce the
common fixed space. -/
theorem four_mul_le_fixedCodim {s : ℕ}
    (hd : Module.finrank (ZMod 2) (SchurField σ) = s) (a : A)
    (ha : IsTransvectionOperator (absoluteActorRepresentation σ A hl a)) :
    4 * s ≤ fixedCodim (normalizerRepresentation σ) A := by
  rw [fixedCodim_eq_schur_mul σ A hl, hd]
  simpa only [Nat.mul_comm s 4] using
    Nat.mul_le_mul_left s (four_le_fixedCodim_of_transvection
      (absoluteActorRepresentation σ A hl) a ha)

variable {F : Type*} [Field F] (J : HermitianForm 3 F)
  (σ : Representation (ZMod 2) J.specialSubgroup V) [σ.IsIrreducible]

/-- The missing outer-operator identification. The equation concerns the
specified literal actor after extension of its actual Schur field. -/
@[expose] def OuterTransposeRealization (s : ℕ) : Prop :=
  AdjointSchurModel J σ s →
    ∀ (A : Subgroup (linearNormalizer σ)), IsElementaryTwo A →
      ∀ hl : ∀ t ∈ A, SchurNormalizer.IsSchurLinear σ t,
      ∀ t : linearNormalizer σ, ∀ ht : t ∈ A,
      (actionImage σ).normalizerMonoidHom t ∉ MulAut.innerSubgroup (actionImage σ) →
      IsTransposeOperator (absoluteActorRepresentation σ A hl ⟨t, ht⟩)

/-- The small-field group and operator identification. Rank at least two must
produce an actual transvection actor, not just an abstract inner automorphism. -/
@[expose] def SmallFieldTransvectionRealization : Prop :=
  AdjointSchurModel J σ 2 →
    ∀ (A : Subgroup (linearNormalizer σ)), IsElementaryTwo A →
      ∀ hl : ∀ t ∈ A, SchurNormalizer.IsSchurLinear σ t,
      2 ≤ rank A → ∃ a : A,
        IsTransvectionOperator (absoluteActorRepresentation σ A hl a)

end Representation.SU3.CubicDegree.SchurOuter.AdjointBounds
