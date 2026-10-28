module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree.TensorWords
public import Theory.Representation.SL3.BinaryFieldDescent
public import Theory.Representation.SL3.BinaryFieldDescent.Fields
public import Theory.Representation.SL3.BinaryFieldDescent.BaseChange
public import Theory.Representation.EndFieldFrobenius

/-!
# Binary descent of the surviving unitary models

A compatible isomorphism between the actual endomorphism field and the matrix
field descends a natural or dual Schur model. The compatibility uses the chosen
embedding, so Frobenius twists are preserved throughout. The Hermitian pairing
identifies the natural action with its F-linear dual after restricting scalars
to F₂. Its coordinate map is conjugation followed by the transpose of the
nondegenerate Gram matrix, then the dot-product identification with covectors.
Thus the final binary intertwiner uses the original Hermitian form and the
identity group automorphism. No classification or degree-minimum assertion is
used to infer an intertwiner.

Source: GLS III, Remark 2.8.8; Aschbacher--Smith K.3.3, printed p.456.
The compatible-field descent follows the existing construction in
Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.SmallConstituents.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open BenderSuzuki.MatrixGroups Representation
open scoped MonoidAlgebra TensorProduct
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.MinimalDegree
variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

private def conjCoordinates (J : HermitianForm 3 F) :
    (Fin 3 → F) ≃ₗ[ZMod 2] (Fin 3 → F) where
  toFun v i := J.conj (v i)
  invFun v i := J.conj (v i)
  left_inv v := funext (fun i => J.conj_involutive (v i))
  right_inv v := funext (fun i => J.conj_involutive (v i))
  map_add' v w := funext (fun i => map_add J.conj (v i) (w i))
  map_smul' c v := funext (fun i => ZMod.map_smul J.conj.toAddMonoidHom c (v i))

private def hermitianDualCoordinates (J : HermitianForm 3 F) :
    (Fin 3 → F) ≃ₗ[ZMod 2] Module.Dual F (Fin 3 → F) :=
  (conjCoordinates J).trans
    (((Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.mkOfDetNeZero
      J.form.transpose (by simpa using J.form_nondegenerate))).toLinearEquiv.restrictScalars
        (ZMod 2)).trans ((dotProductEquiv F (Fin 3)).restrictScalars (ZMod 2)))

private theorem hermitianDualCoordinates_apply (J : HermitianForm 3 F)
    (v w : Fin 3 → F) :
    hermitianDualCoordinates J v w =
      (fun i => J.conj (v i)) ⬝ᵥ (J.form.mulVec w) := by
  change (J.form.transpose.mulVec (fun i => J.conj (v i))) ⬝ᵥ w = _
  rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec]

omit [Algebra (ZMod 2) F] in
private theorem conj_mulVec (J : HermitianForm 3 F)
    (A : Matrix (Fin 3) (Fin 3) F) (v : Fin 3 → F) :
    (fun i => J.conj ((A.mulVec v) i)) =
      (J.conjTranspose A).transpose.mulVec (fun i => J.conj (v i)) := by
  ext i
  simp [Matrix.mulVec, dotProduct, HermitianForm.conjTranspose]

private theorem hermitianDualCoordinates_equivariant (J : HermitianForm 3 F)
    (g : J.specialSubgroup) (v : Fin 3 → F) :
    hermitianDualCoordinates J (natural J (RingHom.id F) g v) =
      (natural J (RingHom.id F)).dual g (hermitianDualCoordinates J v) := by
  apply LinearMap.ext
  intro w
  change hermitianDualCoordinates J (g.val.val.mulVec v) w =
    hermitianDualCoordinates J v ((g⁻¹).val.val.mulVec w)
  rw [hermitianDualCoordinates_apply, hermitianDualCoordinates_apply, conj_mulVec,
    dotProduct_comm, Matrix.dotProduct_transpose_mulVec]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hJ := ((J.mem_specialSubgroup_iff g.val).mp g.property).1
  have hi : g.val.val * (g⁻¹).val.val = 1 := by
    exact congrArg (fun x : J.specialSubgroup => x.val.val) (mul_inv_cancel g)
  have hm : J.conjTranspose g.val.val * J.form = J.form * (g⁻¹).val.val := by
    have h := congrArg (fun A => A * (g⁻¹).val.val) hJ
    simpa only [Matrix.mul_assoc, hi, Matrix.mul_one] using h
  rw [hm]

private def binaryNaturalDualEquiv (J : HermitianForm 3 F) :
    (restrictScalars (k := ZMod 2) (natural J (RingHom.id F))).Equiv
      (restrictScalars (k := ZMod 2) (natural J (RingHom.id F)).dual) :=
  .mk (hermitianDualCoordinates J) (by
    intro g
    apply LinearMap.ext
    intro v
    exact hermitianDualCoordinates_equivariant J g v)

variable {K : Type*} [Field K] [Algebra F K]
private def naturalBaseChange (J : HermitianForm 3 F) :
    (extendScalars K (natural J (RingHom.id F))).Equiv (natural J (algebraMap F K)) :=
  .mk (TensorProduct.piScalarRight F K K (Fin 3)) (by
    intro g
    ext v i
    change (TensorProduct.piScalarRight F K K (Fin 3))
      ((1 : K) ⊗ₜ[F] (natural J (RingHom.id F) g (Pi.single v 1))) i =
      natural J (algebraMap F K) g
        ((TensorProduct.piScalarRight F K K (Fin 3)) ((1 : K) ⊗ₜ[F] (Pi.single v 1))) i
    simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      Algebra.smul_def, mul_one]
    change (algebraMap F K) ((g.val.val.mulVec (Pi.single v 1)) i) =
      ((g.val.val.map (algebraMap F K)).mulVec
        (fun j => (algebraMap F K) ((Pi.single v 1 : Fin 3 → F) j))) i
    simp [Matrix.mulVec, dotProduct])

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] [Finite F]
  (J : HermitianForm 3 F)
  (σ : Representation (ZMod 2) J.specialSubgroup V) [IsIrreducible σ]
  [Algebra (Module.End (ZMod 2)[J.specialSubgroup] σ.asModule) K]

open Representation.BinaryFieldDescent
omit [Algebra F K] in
/-- Descent of either singleton Schur model constructs actual binary natural
coordinates. All embeddings, including Frobenius twists, are retained. -/
theorem isNatural_of_absolute_natural {s : ℕ}
    (hcard : Nat.card F = (2 ^ s) ^ 2) (hs : schurDegree 2 σ = 2 * s)
    (h : ∃ ι : F →+* K,
      Nonempty ((extendScalars K σ.endFieldRep).Equiv (natural J ι)) ∨
      Nonempty ((extendScalars K σ.endFieldRep).Equiv (natural J ι).dual)) :
    IsNatural J σ := by
  obtain ⟨ι, h⟩ := h
  let : Algebra F K := ι.toAlgebra
  let E := Module.End (ZMod 2)[J.specialSubgroup] σ.asModule
  have hc : Nat.card F = Nat.card E := by
    let : Module.Finite (ZMod 2) E := Module.Finite.of_finite
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E)
    change Nat.card E = Nat.card (ZMod 2) ^ schurDegree 2 σ at he
    rw [he, hs, Nat.card_zmod, hcard, ← pow_mul, Nat.mul_comm s 2]
  obtain ⟨e, he⟩ := FiniteField.exists_compatible_equiv_of_card_eq
    (algebraMap E K) ι hc
  let := scalarModule σ e
  let : Finite V := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) V)
  let : Module.Finite F V := Module.Finite.of_finite
  let τ := scalarRep σ e
  let eS := scalarExtensionEquiv σ e he
  let eN := naturalBaseChange (K := K) J
  have heb : Nonempty (σ.Equiv
      (restrictScalars (k := ZMod 2) (natural J (RingHom.id F)))) := by
    rcases h with h | h
    · obtain ⟨ea⟩ := h
      obtain ⟨ed⟩ := equiv_of_extendScalars (K := K) τ
        (natural J (RingHom.id F)) ⟨eS.symm.trans (ea.trans eN.symm)⟩
      simpa only [τ, restrict_scalarRep] using Nonempty.intro (restrictBinaryEquiv ed)
    · obtain ⟨ea⟩ := h
      let eD := (dualBaseChange (K := K) (natural J (RingHom.id F))).trans (dualEquiv eN)
      obtain ⟨ed⟩ := equiv_of_extendScalars (K := K) τ
        (natural J (RingHom.id F)).dual ⟨eS.symm.trans (ea.trans eD.symm)⟩
      have eb := (restrictBinaryEquiv ed).trans (binaryNaturalDualEquiv J).symm
      simpa only [τ, restrict_scalarRep] using Nonempty.intro eb
  obtain ⟨eb⟩ := heb
  refine ⟨MulEquiv.refl _, eb.toLinearEquiv, ?_⟩
  intro g v
  exact LinearMap.congr_fun (eb.isIntertwining' g) v
end CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.MinimalDegree
