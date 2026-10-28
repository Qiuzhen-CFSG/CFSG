module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Remaining
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Inner.Reduction
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.FieldDescent
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.BinaryIdentification.AdjointBaseChange

/-!
# Descending the single-adjoint word to its defining field

The existing inner-word reduction supplies an actual absolute adjoint
intertwiner, including the coefficient twist. The repetition identity makes
the defining field and Schur field have the same order. Matching their
embeddings and descending the actual trace-kernel base-change equivalence
therefore identifies the original binary action with the restriction of the
adjoint over the defining field. Scalar multiplication on this model is a
commuting intertwiner, so every Schur-linear actor is coefficient-linear.
No faithfulness on the SL₃ cover, normalizer form or displacement premise
is used.

Source: GLS III, Remark 2.8.8 and Example 2.8.10(c); Guralnick–Malle,
Classification of 2F-modules II, Proposition 4.8 step 3A, manuscript p.27.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender
open Representation.SL3.BinaryDefiningFactors Representation.BinaryFieldDescent
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open scoped MatrixGroups TensorProduct
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint
variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V) [IsIrreducible σ]

/-- The binary restriction of the actual trace-zero conjugation action. -/
abbrev binaryRep : Representation (ZMod 2) SL(3,B.Carrier) (AdjointSpace B.Carrier) :=
  restrictScalars (k := ZMod 2) (factorRep (RingHom.id B.Carrier) .adjoint)

/-- A single-adjoint repeated word descends with the original SL₃ marking. -/
theorem single_adjoint_binary_model (M : RepeatedModel B σ)
    (hM : SingleAdjoint B σ M) : Nonempty (σ.Equiv (binaryRep B)) := by
  obtain ⟨ha, hb, ht⟩ := hM
  obtain ⟨ι, ⟨ea⟩, _⟩ := Inner.single_adjoint_model B σ M ha hb ht
  have hE : schurDegree σ = B.degree := by
    simpa only [ht, mul_one] using M.field_degree.symm
  let : Algebra B.Carrier (SplittingField σ) := ι.toAlgebra
  obtain ⟨e, he⟩ := exists_natural_schur_equiv σ B.degree B.card_eq hE ι
  let := scalarModule σ e
  let : Finite V := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) V)
  let : Module.Finite B.Carrier V := Module.Finite.of_finite
  let τ := scalarRep σ e
  let eS := scalarExtensionEquiv σ e he
  let eN := adjointBaseChange (F := B.Carrier) (K := SplittingField σ)
  obtain ⟨ed⟩ := equiv_of_extendScalars (K := SplittingField σ) τ
    (factorRep (RingHom.id B.Carrier) .adjoint) ⟨eS.symm.trans (ea.trans eN.symm)⟩
  have eb := restrictBinaryEquiv (W := AdjointSpace B.Carrier) ed
  simpa only [τ, restrict_scalarRep, binaryRep] using Nonempty.intro eb


omit [FiniteDimensional (ZMod 2) V] [IsIrreducible σ] in
/-- Commuting with the actual Schur ring implies coefficient linearity on an
actual binary adjoint model. This does not assert an inner automorphism form. -/
theorem schurLinear_smul (e : σ.Equiv (binaryRep B))
    (t : linearNormalizer σ) (ht : SchurNormalizer.IsSchurLinear σ t)
    (c : B.Carrier) (x : AdjointSpace B.Carrier) :
    e (t.val.val (e.symm (c • x))) = c • e (t.val.val (e.symm x)) := by
  let s : IntertwiningMap (binaryRep B) (binaryRep B) := {
    toLinearMap := (c • (LinearMap.id : AdjointSpace B.Carrier →ₗ[B.Carrier]
      AdjointSpace B.Carrier)).restrictScalars (ZMod 2)
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro y
      change c • factorRep (RingHom.id B.Carrier) .adjoint g y =
        factorRep (RingHom.id B.Carrier) .adjoint g (c • y)
      exact (map_smul _ _ _).symm }
  let f := e.symm.toIntertwiningMap.comp (s.comp e.toIntertwiningMap)
  have h := congrArg e (ht f (e.symm x))
  change e (t.val.val (e.symm (c • e (e.symm x)))) =
    e (e.symm (c • e (t.val.val (e.symm x)))) at h
  have he (y : AdjointSpace B.Carrier) : e (e.symm y) = y :=
    e.toLinearEquiv.apply_symm_apply y
  simpa only [he] using h

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint
