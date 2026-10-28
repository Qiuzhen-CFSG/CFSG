module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixCertificates
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.RemainingGeneratorOrders
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792

/-!
# Prescribed large Mathieu models from native subquotient certificates

The degree-320 convention uses raw ATLAS matrices at inverse native generators.
The checked square and cube identities convert the positive-generator matrices
A and B² into that exact convention. The two larger models retain the transposes
of the raw matrices at the positive native generators. The first 320 embedding only needs nonvanishing: density proves injectivity,
and the checked literal contragredient constructs the second model. Applying
the existing density and trace-separation theorems gives the binary consumers.

These are conditional construction theorems: the source actions must be genuine
native representations and every field of each subquotient certificate must be
proved. They assert neither unconditional native realizations nor
`LargeModelsExist`. The native presentations and all their APIs are unchanged.

Sources: James, J. Algebra 27 (1973), 57–111; GM02 Proposition 5.1 and
Aschbacher–Smith K.4, printed p.457. The fixed ATLAS matrices retain the
attributions in `Degree320Pair/source/README.md` and
`Degrees12421792/source/README.md`.
-/

public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels
open Sporadic.Mathieu
open NativeSubquotient

private theorem matrix_at_inverse {d : ℕ}
    (ρ : Representation (ZMod 2) M24 (Fin d → ZMod 2)) (g : M24)
    (M N : Matrix (Fin d) (Fin d) (ZMod 2))
    (hM : LinearMap.toMatrix' (ρ g) = M) (hNM : N * M = 1) :
    LinearMap.toMatrix' (ρ g⁻¹) = N := by
  have he : Matrix.toLin' N * ρ g = 1 := by
    apply LinearMap.toMatrix'.injective
    rw [LinearMap.toMatrix'_mul, LinearMap.toMatrix'_toLin', hM, hNM,
      LinearMap.toMatrix'_one]
  have hright : ρ g * ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hn : Matrix.toLin' N = ρ g⁻¹ := by
    calc
      Matrix.toLin' N = Matrix.toLin' N * (ρ g * ρ g⁻¹) := by rw [hright, mul_one]
      _ = ρ g⁻¹ := by rw [← mul_assoc, he, one_mul]
  rw [← hn, LinearMap.toMatrix'_toLin']

namespace Degree320Pair

/-- Native positive-generator matrices A and B² give precisely the raw ATLAS
matrices at the inverse generators used by the published degree-320 contract. -/
theorem realizes_of_positive_generator_matrices (variant : Bool)
    (ρ : Representation (ZMod 2) M24 Space)
    (hA : LinearMap.toMatrix' (ρ Degree220Pair.generatorA) = matrixA variant)
    (hB : LinearMap.toMatrix' (ρ Degree220Pair.generatorB) = matrixB variant ^ 2) :
    Realizes variant ρ := by
  have hAA : matrixA variant * matrixA variant = 1 := by
    have h := MatrixRelationCertificate.rowRelatorValues_zero variant
    change matrixA variant ^ 2 = 1 at h
    simpa only [pow_two] using h
  have hBBB : matrixB variant * matrixB variant ^ 2 = 1 := by
    rw [← pow_succ', MatrixRelationCertificate.cube_matrixB]
  exact ⟨matrix_at_inverse ρ Degree220Pair.generatorA _ _ hA hAA,
    matrix_at_inverse ρ Degree220Pair.generatorB _ _ hB hBBB⟩

/-- Construct the raw inverse-generator action from an invariant native
subquotient, with both source invariance and quotient invariance proved. -/
theorem action_of_subquotient_certificate {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {u : ℕ} (variant : Bool)
    (σ : Representation (ZMod 2) M24 V)
    (c : Certificate (u := u) σ (matrixA variant) (matrixB variant ^ 2)) :
    ∃ ρ : Representation (ZMod 2) M24 Space, Realizes variant ρ := by
  obtain ⟨ρ, hA, hB⟩ := c.realization
  exact ⟨ρ, realizes_of_positive_generator_matrices variant ρ hA hB⟩


/-- The checked literal contragredient identities construct the second native
model from the first, avoiding a second family of subquotient certificates. -/
theorem actionsExist_of_first_action
    (ρ : Representation (ZMod 2) M24 Space) (hρ : Realizes false ρ) : ActionsExist := by
  let dual : Representation (ZMod 2) M24 Space :=
    Matrix.toLinAlgEquiv'.toMonoidHom.comp
      { toFun g := (LinearMap.toMatrix' (ρ g⁻¹)).transpose
        map_one' := by simp
        map_mul' g h := by
          simp only [mul_inv_rev, map_mul, LinearMap.toMatrix'_mul, Matrix.transpose_mul] }
  have hA : LinearMap.toMatrix' (ρ actorA⁻¹) = matrixA false := by
    apply matrix_at_inverse ρ actorA (matrixA false) _ hρ.1
    simpa only [← pow_two] using MatrixRelationCertificate.square_matrixA_false
  have hB : LinearMap.toMatrix' (ρ actorB⁻¹) = matrixB false ^ 2 := by
    apply matrix_at_inverse ρ actorB (matrixB false) _ hρ.2
    rw [← pow_succ, MatrixRelationCertificate.cube_matrixB]
  have hd : Realizes true dual := by
    constructor
    · change LinearMap.toMatrix' (Matrix.toLin' _) = _
      rw [LinearMap.toMatrix'_toLin']
      change (LinearMap.toMatrix' (ρ actorA⁻¹)).transpose = matrixA true
      rw [hA, MatrixRelationCertificate.matrixA_true_eq_transpose_false]
    · change LinearMap.toMatrix' (Matrix.toLin' _) = _
      rw [LinearMap.toMatrix'_toLin']
      change (LinearMap.toMatrix' (ρ actorB⁻¹)).transpose = matrixB true
      rw [hB, MatrixRelationCertificate.matrixB_true_eq_transpose_square_false]
  intro variant
  cases variant
  · exact ⟨ρ, hρ⟩
  · exact ⟨dual, hd⟩


private def kernelPreserving (W : Submodule (ZMod 2) Space) : Subalgebra (ZMod 2) Mat where
  carrier := {M | ∀ x ∈ W, M.mulVec x ∈ W}
  zero_mem' := by intro x _; simp
  one_mem' := by intro x hx; simpa using hx
  add_mem' := by
    intro M N hM hN x hx
    simpa only [Matrix.add_mulVec] using W.add_mem (hM x hx) (hN x hx)
  mul_mem' := by
    intro M N hM hN x hx
    simpa only [← Matrix.mulVec_mulVec] using hM _ (hN x hx)
  algebraMap_mem' := by
    intro r x hx
    simpa only [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
      using W.smul_mem r hx

/-- Density makes a nonzero first-model intertwiner injective, so the concrete
320a embedding needs no large left-inverse certificate. -/
theorem first_embedding_injective {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) M24 V) (E : Space →ₗ[ZMod 2] V) (hE : E ≠ 0)
    (hA : (σ Degree220Pair.generatorA).comp E = E.comp (Matrix.toLin' (matrixA false)))
    (hB : (σ Degree220Pair.generatorB).comp E = E.comp (Matrix.toLin' (matrixB false ^ 2))) :
    Function.Injective E := by
  have hmem (g : M24) (M : Mat)
      (h : (σ g).comp E = E.comp (Matrix.toLin' M)) : M ∈ kernelPreserving E.ker := by
    intro x hx
    change E (M.mulVec x) = 0
    have he := congrArg (fun f => f x) h
    change σ g (E x) = E (M.mulVec x) at he
    rw [LinearMap.mem_ker.mp hx, map_zero] at he
    exact he.symm
  have hMA := hmem Degree220Pair.generatorA (matrixA false) hA
  have hMB2 := hmem Degree220Pair.generatorB (matrixB false ^ 2) hB
  have hMB : matrixB false ∈ kernelPreserving E.ker := by
    have h := (kernelPreserving E.ker).pow_mem hMB2 2
    rw [← pow_mul, show (2 : ℕ) * 2 = 3 + 1 from rfl, pow_succ,
      MatrixRelationCertificate.cube_matrixB, one_mul] at h
    exact h
  have hfull : kernelPreserving E.ker = ⊤ := by
    apply top_unique
    rw [← generatorDensity false]
    apply Algebra.adjoin_le
    rintro _ (rfl | rfl)
    · exact hMA
    · exact hMB
  apply LinearMap.ker_eq_bot.mp
  by_contra hn
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hz
    push Not at hz
    exact hx0 (funext hz)
  have hi1 : x i = 1 := by
    have hb : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
    exact (hb (x i)).resolve_left hi
  apply hE
  apply LinearMap.ext
  intro y
  have hm : Matrix.vecMulVec y (Pi.single i 1) ∈ kernelPreserving E.ker := by
    rw [hfull]
    trivial
  have hy := hm x hx
  simpa [Matrix.vecMulVec_mulVec, hi1] using hy

end Degree320Pair

/-- Apply native subquotient constructions to the literal binary-pair consumer.
The existing density and trace separation discharge all other premises. -/
theorem pair320_of_subquotient_certificates {V : Bool → Type*}
    [∀ b, AddCommGroup (V b)] [∀ b, Module (ZMod 2) (V b)] {u : Bool → ℕ}
    (σ : ∀ b, Representation (ZMod 2) M24 (V b))
    (c : ∀ b, Certificate (u := u b) (σ b)
      (Degree320Pair.matrixA b) (Degree320Pair.matrixB b ^ 2)) :
    Nonempty (BinaryPair 320) :=
  pair320_of_certificates (fun b => Degree320Pair.action_of_subquotient_certificate b (σ b) (c b))
    Degree320Pair.generatorDensity Degree320Pair.traceSeparation


/-- One native subquotient certificate suffices for the entire degree-320 pair;
the second action is its checked literal contragredient. -/
theorem pair320_of_first_subquotient_certificate {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] {u : ℕ}
    (σ : Representation (ZMod 2) M24 V)
    (c : Certificate (u := u) σ (Degree320Pair.matrixA false)
      (Degree320Pair.matrixB false ^ 2)) : Nonempty (BinaryPair 320) := by
  obtain ⟨ρ, hρ⟩ := Degree320Pair.action_of_subquotient_certificate false σ c
  exact pair320_of_certificates (Degree320Pair.actionsExist_of_first_action ρ hρ)
    Degree320Pair.generatorDensity Degree320Pair.traceSeparation


/-- The actual 320-pair consumer needs only a nonzero native embedding and its
two positive-generator equations. Density and literal duality supply rank and
the second model, avoiding both a rank inverse and a second matrix-map family. -/
theorem pair320_of_first_nonzero_embedding {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) M24 V)
    (E : Degree320Pair.Space →ₗ[ZMod 2] V) (hE : E ≠ 0)
    (hA : (σ Degree220Pair.generatorA).comp E =
      E.comp (Matrix.toLin' (Degree320Pair.matrixA false)))
    (hB : (σ Degree220Pair.generatorB).comp E =
      E.comp (Matrix.toLin' (Degree320Pair.matrixB false ^ 2))) :
    Nonempty (BinaryPair 320) := by
  obtain ⟨ρ, hρA, hρB⟩ := NativeSubquotient.of_embedding σ _ _ E
    (Degree320Pair.first_embedding_injective σ E hE hA hB) hA hB
  have hρ := Degree320Pair.realizes_of_positive_generator_matrices false ρ hρA hρB
  exact pair320_of_certificates (Degree320Pair.actionsExist_of_first_action ρ hρ)
    Degree320Pair.generatorDensity Degree320Pair.traceSeparation

/-- Apply the two transposed native constructions to the largest-model consumer.
Only the finite subquotient certificates remain; both densities are proved. -/
theorem models12421792_of_subquotient_certificates
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] {u w : ℕ}
    (σ : Representation (ZMod 2) M24 V) (τ : Representation (ZMod 2) M24 W)
    (c : Certificate (u := u) σ
      Degrees12421792.Data1242.first.transpose Degrees12421792.Data1242.second.transpose)
    (d : Certificate (u := w) τ
      Degrees12421792.Data1792.first.transpose Degrees12421792.Data1792.second.transpose) :
    Nonempty (BinaryModel 1242) ∧ Nonempty (BinaryModel 1792) := by
  obtain ⟨ρ, hA, hB⟩ := c.realization
  obtain ⟨π, hC, hD⟩ := d.realization
  exact models12421792_of_matrix_certificates ⟨ρ, hA, hB⟩ ⟨π, hC, hD⟩
    Degrees12421792.density1242 Degrees12421792.density1792

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels
