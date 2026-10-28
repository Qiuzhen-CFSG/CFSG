module

public import Theory.Representation.HigmanSims.Twenty.Absolute.Certificate
public import Theory.Representation.HigmanSims.Twenty.Absolute.RankOne
public import Theory.Representation.AbsolutelyIrreducible
public import Mathlib.Algebra.Field.ZMod

/-!
# Absolute irreducibility of the literal HS degree-twenty action

The checked Horner polynomial in a sum of four generator words produces a
rank-one operator. Its twenty column and row translates form bases, with
checked inverse matrices. Taking linear combinations and products gives
every matrix unit, hence every endomorphism. The scalar-extension density
theorem then proves irreducibility on the actual tensor product over the
algebraic closure (and over every field extension).

Source: ATLAS HSG1-f2r20B0; the untrusted certificate and its discovery are
preserved in `Twenty/source/`. No carrier comparison or classification of
other degree-twenty representations is used.
-/

public section
namespace Sporadic.LeechRelated.HS.Twenty

/-- The literal two generators generate the full matrix algebra. -/
theorem matrix_algebra_eq_top
    (A : Subalgebra (ZMod 2) BinaryMatrix) (ha : aMatrix ∈ A) (hb : bMatrix ∈ A) :
    A = ⊤ := by
  exact Absolute.eq_top_of_rankOne A
    Absolute.Certificate.columnMatrix Absolute.Certificate.columnInverse
    Absolute.Certificate.rowMatrix Absolute.Certificate.rowInverse
    Absolute.Certificate.u Absolute.Certificate.r
    Absolute.Certificate.column_inverse Absolute.Certificate.row_inverse
    Absolute.Certificate.pairing
    (Absolute.Certificate.column_mem A ha hb) (Absolute.Certificate.row_mem A ha hb)

/-- The tautological matrix-group representation generates every endomorphism. -/
theorem density : Algebra.adjoin (ZMod 2) (Set.range representation) = ⊤ := by
  let P := Algebra.adjoin (ZMod 2) (Set.range representation)
  let L : BinaryMatrix ≃ₐ[ZMod 2] Module.End (ZMod 2) Vector := Matrix.toLinAlgEquiv'
  let Q := P.comap L.toAlgHom
  have ha : aMatrix ∈ Q := by
    exact Algebra.subset_adjoin ⟨a, rfl⟩
  have hb : bMatrix ∈ Q := by
    exact Algebra.subset_adjoin ⟨b, rfl⟩
  have hQ := matrix_algebra_eq_top Q ha hb
  apply top_unique
  intro f _
  have hf : L.symm f ∈ Q := by rw [hQ]; trivial
  change L (L.symm f) ∈ P at hf
  simpa only [AlgEquiv.apply_symm_apply] using hf

/-- Absolute irreducibility for the actual tensor-product scalar extension. -/
theorem absolutelyIrreducible : representation.IsAbsolutelyIrreducible := by
  refine ⟨?_⟩
  apply Representation.irreducible_of_jacobson_density_surjective
  exact (Representation.extendScalars_surj_iff (AlgebraicClosure (ZMod 2))
    representation).mp density

/-- The same literal action is irreducible after every field extension. -/
theorem irreducible_extendScalars (F : Type*) [Field F] [Algebra (ZMod 2) F] :
    (Representation.extendScalars F representation).IsIrreducible := by
  let := absolutelyIrreducible
  exact Representation.IsAbsolutelyIrreducible.irreducible_of_extension representation F

end Sporadic.LeechRelated.HS.Twenty
