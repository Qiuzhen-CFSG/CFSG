module

public import Theory.Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose.ScalarRigidity
public import Theory.Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose.Geometry

/-!
# From adjoint graph intertwiners to the literal outer operator

The actual Schur-linear actor and a geometric graph operator intertwine the
same pairs of group representatives. Their ratio is scalar by irreducibility
over the algebraic closure of the Schur field. Both square to one, so that
scalar is one in characteristic two. The given representation equivalence
therefore supplies coordinates for the actual actor, and the three transpose
equations give its fixed-codimension bound.

The matrix-group construction of the graph intertwiner is supplied by the
adjacent geometry module from outer-involution normal form, unitary descent,
and basis transport. The conditional reduction is retained for consumers that
provide a different graph operator; the concrete finite-field theorem below
uses that construction directly. No displacement bound or offender inequality
is used.

Source: Guralnick--Malle, Classification of 2F-modules II, Proposition 4.11,
internal pp.31--32.
-/

public section
open BenderSuzuki.MatrixGroups Representation Representation.BinaryOffender Subgroup
open Representation.FrobeniusTensor

namespace Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose
variable {F V : Type*} [Field F] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (J : HermitianForm 3 F)
  (σ : Representation (ZMod 2) J.specialSubgroup V) [σ.IsIrreducible]

/-- A geometric graph intertwiner on the adjoint model identifies the
specified literal outer actor, through the supplied adjoint Schur model. -/
theorem outerTransposeRealization_of_graphIntertwiners
    (hgeom : ∀ (ι : F →+* Closure σ) (t : linearNormalizer σ),
      t ^ 2 = 1 → (actionImage σ).normalizerMonoidHom t ∉
        MulAut.innerSubgroup (actionImage σ) →
      AdjointGraphIntertwiner J ι (actionHom σ) ((actionImage σ).normalizerMonoidHom t)) (s : ℕ) :
    OuterTransposeRealization J σ s := by
  intro hm A hA hl t ht hout
  obtain ⟨ι, ⟨e⟩⟩ := hm.model
  let : IsElementaryAbelian 2 A := hA.2
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t ht
  have ha2 : (⟨t, ht⟩ : A) ^ 2 = 1 := Subtype.ext ht2
  exact isTransposeOperator_of_adjointGraphIntertwiner J σ A hl ι e ⟨t, ht⟩ ha2
    (hgeom ι t ht2 hout)

/-- Every outer involution of a central-kernel binary SU₃ action is realized by
the literal transpose operator on the adjoint model.  The geometric operator
is constructed on the actual trace-zero matrix space, and scalar ambiguity is
removed by the supplied Schur intertwiner. -/
theorem outerTransposeRealization
    [Finite F] {s : ℕ} (hs : 2 ≤ s) (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (hk : σ.ker ≤ center J.specialSubgroup) :
    OuterTransposeRealization J σ s := by
  apply outerTransposeRealization_of_graphIntertwiners J σ (s := s)
  intro ι t ht2 hout
  exact adjointGraphIntertwiner_of_outer_involution J hs hcard hconj σ hk ι t ht2 hout

/-- Application to the actual common fixed space: one outer actor gives
three independent equations over the Schur field. -/
theorem three_mul_le_fixedCodim_of_graphIntertwiners {s : ℕ}
    (hm : AdjointSchurModel J σ s)
    (hgeom : ∀ (ι : F →+* Closure σ) (t : linearNormalizer σ),
      t ^ 2 = 1 → (actionImage σ).normalizerMonoidHom t ∉
        MulAut.innerSubgroup (actionImage σ) →
      AdjointGraphIntertwiner J ι (actionHom σ) ((actionImage σ).normalizerMonoidHom t))
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hl : ∀ t ∈ A, SchurNormalizer.IsSchurLinear σ t)
    (t : linearNormalizer σ) (ht : t ∈ A)
    (hout : (actionImage σ).normalizerMonoidHom t ∉
      MulAut.innerSubgroup (actionImage σ)) :
    3 * s ≤ fixedCodim (normalizerRepresentation σ) A :=
  three_mul_le_fixedCodim σ A hl hm.fieldDegree ⟨t, ht⟩
    (outerTransposeRealization_of_graphIntertwiners J σ hgeom s hm A hA hl t ht hout)

/-- Conditional application to both bounds. The small-field transvection
realization is retained as the independent premise of the owning assembly. -/
theorem adjointFixedSpaceBounds_of_graphIntertwiners {s : ℕ}
    (hgeom : ∀ (ι : F →+* Closure σ) (t : linearNormalizer σ),
      t ^ 2 = 1 → (actionImage σ).normalizerMonoidHom t ∉
        MulAut.innerSubgroup (actionImage σ) →
      AdjointGraphIntertwiner J ι (actionHom σ) ((actionImage σ).normalizerMonoidHom t))
    (hi : s = 2 → SmallFieldTransvectionRealization J σ) :
    AdjointFixedSpaceBounds J σ s := by
  intro hm A hA hl t ht hout
  constructor
  · exact three_mul_le_fixedCodim_of_graphIntertwiners J σ hm hgeom A hA hl t ht hout
  · rintro rfl htwo
    obtain ⟨a, ha⟩ := hi rfl hm A hA hl htwo
    exact four_mul_le_fixedCodim σ A hl hm.fieldDegree a ha

end Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose
