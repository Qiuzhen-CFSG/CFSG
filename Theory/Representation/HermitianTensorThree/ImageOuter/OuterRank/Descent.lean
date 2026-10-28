module

public import Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.Actions
public import Theory.Representation.HermitianTensorThree.ImageOuter.FieldSections.Coordinates
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.FieldDescent.FixedSpace

/-!
# Descent of Hermitian semilinear involutions

Suppose a binary automorphism of the literal Hermitian space is the
congruence action of a GL₃ matrix followed by coefficient conjugation.
If its square is one, the matrix product g σ(g) fixes every Hermitian
matrix, hence is a norm-one scalar λ. Associativity and invertibility
force σ(λ) = λ, and characteristic two then gives λ = 1.

The semilinear involution v ↦ g σ(v) therefore has a basis of fixed vectors.
Writing those vectors as the columns of h gives g σ(h) = h. Congruence by
h⁻¹ belongs to the actual binary normalizer and conjugates the original
automorphism to the marked field swap. No normalizer coverage, source
overgroup membership, or centralizer identification is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.4.2 setup
and the outer-involution assertion in the proof of H.4.4(6), printed
pp.380–381 of `refs/quasithin.pdf`. The source assembly must separately
establish the coefficient-conjugation expression for its outer involutions.
-/

public section
noncomputable section
namespace Representation.HermitianTensorThree.ImageOuter.OuterRank
open Matrix
variable (n : ℕ) [NeZero n]

private theorem map_sigma_twice (A : Mat n) :
    (A.map (sigma n)).map (sigma n) = A := by
  ext j k
  exact sigma_involutive n (A j k)

private theorem cocycle_of_involution
    (i : Space n ≃ₗ[ZMod 2] Space n) (hi : i ^ 2 = 1)
    (g : GeneralLinearGroup (Fin 3) (E n))
    (hig : ∀ X : Space n, (i X).val = g.val * X.val.map (sigma n) * adjoint n g.val) :
    g.val * g.val.map (sigma n) = 1 := by
  have hfix (X : Space n) :
      (g.val * g.val.map (sigma n)) * X.val *
        adjoint n (g.val * g.val.map (sigma n)) = X.val := by
    have h := congrArg (fun e : Space n ≃ₗ[ZMod 2] Space n => (e X).val) hi
    change (i (i X)).val = X.val at h
    rw [hig, hig, Matrix.map_mul, Matrix.map_mul, map_sigma_twice,
      ← adjoint_map] at h
    rw [adjoint_mul]
    simpa only [Matrix.mul_assoc] using h
  obtain ⟨c, hc, hnorm⟩ := eq_scalar_of_fixes_hermitian n _ hfix
  have hcmap : g.val.map (sigma n) * g.val = Matrix.scalar (Fin 3) (sigma n c) := by
    have h := congrArg (fun A : Mat n => A.map (sigma n)) hc
    rw [Matrix.map_mul, map_sigma_twice] at h
    calc
      _ = (Matrix.scalar (Fin 3) c).map (sigma n) := h
      _ = _ := by
        ext j k
        by_cases hjk : j = k
        · subst k; simp
        · simp [Matrix.scalar_apply, hjk]
  have hcomm : Matrix.scalar (Fin 3) c * g.val =
      Matrix.scalar (Fin 3) (sigma n c) * g.val := by
    rw [Matrix.scalar_comm (sigma n c) (Commute.all _), ← hcmap, ← Matrix.mul_assoc, hc]
  have hscalar := congrArg (fun A : Mat n => A * g.inv) hcomm
  simp only [Matrix.mul_assoc, g.val_inv, mul_one] at hscalar
  have hcs : c = sigma n c := by
    simpa using congrArg (fun A : Mat n => A 0 0) hscalar
  have hc1 : c = 1 := by
    rw [← hcs] at hnorm
    rcases mul_self_eq_one_iff.mp hnorm with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  simpa only [hc1, map_one] using hc

private def twist (g : GeneralLinearGroup (Fin 3) (E n)) : Natural n →+ Natural n where
  toFun v := g.val *ᵥ (sigma n ∘ v)
  map_zero' := by simp
  map_add' v w := by
    change g.val *ᵥ (sigma n ∘ (v + w)) = _
    have he : sigma n ∘ (v + w) = (sigma n ∘ v) + (sigma n ∘ w) := by ext j; simp
    rw [he, Matrix.mulVec_add]

private theorem exists_fixed_matrix (g : GeneralLinearGroup (Fin 3) (E n))
    (hg : g.val * g.val.map (sigma n) = 1) :
    ∃ h : GeneralLinearGroup (Fin 3) (E n), g.val * h.val.map (sigma n) = h.val := by
  classical
  have hσ : sigma n ≠ 1 := by
    obtain ⟨a, ha⟩ := FieldSections.exists_sigma_ne n
    intro he
    exact ha (congrArg (fun e : E n ≃+* E n => e a) he)
  have hT (a : E n) (v : Natural n) :
      twist n g (a • v) = sigma n a • twist n g v := by
    change g.val *ᵥ (sigma n ∘ (a • v)) = _
    have he : sigma n ∘ (a • v) = sigma n a • (sigma n ∘ v) := by ext j; simp
    rw [he, Matrix.mulVec_smul]
    rfl
  have hTT (v : Natural n) : twist n g (twist n g v) = v := by
    have he : sigma n ∘ (g.val *ᵥ (sigma n ∘ v)) = g.val.map (sigma n) *ᵥ v := by
      ext j
      change (sigma n).toRingHom ((g.val *ᵥ (sigma n ∘ v)) j) = _
      rw [(sigma n).toRingHom.map_mulVec]
      simp only [Function.comp_def, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      rw [show (fun x => sigma n (sigma n (v x))) = v from
        funext (fun x => sigma_involutive n (v x))]
    change g.val *ᵥ (sigma n ∘ (g.val *ᵥ (sigma n ∘ v))) = v
    rw [he, Matrix.mulVec_mulVec, hg, Matrix.one_mulVec]
  obtain ⟨s, b, hb⟩ :=
    Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.FieldDescent.exists_fixed_basis
      (sigma n) hσ (twist n g) hT hTT
  let std := Pi.basisFun (E n) (Fin 3)
  let b' := b.reindex (b.indexEquiv std)
  let h : GeneralLinearGroup (Fin 3) (E n) :=
    ⟨std.toMatrix b', b'.toMatrix std, std.toMatrix_mul_toMatrix_flip b',
      b'.toMatrix_mul_toMatrix_flip std⟩
  refine ⟨h, ?_⟩
  have hcol (j k : Fin 3) : h.val j k = b' k j := by
    simp [h, std, Module.Basis.toMatrix_apply]
  ext j k
  simp only [Matrix.mul_apply, Matrix.map_apply, hcol]
  have hk := congrFun (hb ((b.indexEquiv std).symm k)) j
  change (∑ x, g.val j x * sigma n (b ((b.indexEquiv std).symm k) x)) =
    b ((b.indexEquiv std).symm k) j at hk
  simpa only [b', Module.Basis.reindex_apply] using hk

/-- A semilinear Hermitian involution is conjugate to the marked field swap
by an actual binary congruence in the full normalizer. -/
theorem exists_conj_fieldSwapBinary_of_sigma_expression
    (i : Space n ≃ₗ[ZMod 2] Space n) (hi : i ^ 2 = 1)
    (g : GeneralLinearGroup (Fin 3) (E n))
    (hig : ∀ X : Space n, (i X).val = g.val * X.val.map (sigma n) * adjoint n g.val) :
    ∃ c ∈ binaryNormalizer n, MulAut.conj c i = fieldSwapBinary n := by
  obtain ⟨h, hh⟩ := exists_fixed_matrix n g (cocycle_of_involution n i hi g hig)
  have hinter : i * binaryCongruence n h = binaryCongruence n h * fieldSwapBinary n := by
    apply LinearEquiv.ext
    intro X
    apply Subtype.ext
    change (i (binaryCongruence n h X)).val =
      (binaryCongruence n h (fieldSwapBinary n X)).val
    rw [hig, binaryCongruence_apply, binaryCongruence_apply]
    change g.val * (h.val * X.val * adjoint n h.val).map (sigma n) * adjoint n g.val =
      h.val * (fieldSwap n X).val * adjoint n h.val
    rw [fieldSwap_eq_map, Matrix.map_mul, Matrix.map_mul, ← adjoint_map]
    calc
      _ = (g.val * h.val.map (sigma n)) * X.val.map (sigma n) *
          adjoint n (g.val * h.val.map (sigma n)) := by
        rw [adjoint_mul]
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hh]
  refine ⟨binaryCongruence n h⁻¹, binaryCongruence_mem_normalizer n h⁻¹, ?_⟩
  rw [MulAut.conj_apply, map_inv, inv_inv, mul_assoc, hinter]
  simp only [← mul_assoc, inv_mul_cancel, one_mul]
end Representation.HermitianTensorThree.ImageOuter.OuterRank
