module

public import Theory.Representation.HermitianTensorThree.ImageOuter.FieldSections.Coordinates

/-!
# The pointwise centralizer of the field-fixed space

Assuming the explicit normalizer-coverage contract, a normalizer element
fixing the symmetric Hermitian matrices has trivial action on their
coefficients. Its congruence matrix is a norm-one scalar. A coefficient
automorphism fixing F in the quadratic extension E is either identity or
σ. Hence the pointwise stabilizer is exactly the marked involution group,
also relative to every source overgroup containing that involution.

Source: Aschbacher–Smith H.4.4(6), printed pp.380–381. Coverage remains an
explicit hypothesis here, to be discharged by the normalizer theorem.
-/

@[expose] public section
noncomputable section
namespace Representation.HermitianTensorThree.ImageOuter.FieldSections
variable (n : ℕ) [NeZero n]

/-- The literal pointwise stabilizer of C_V(σ) in the binary linear group. -/
def pointwiseFixed : Subgroup (Space n ≃ₗ[ZMod 2] Space n) where
  carrier := {e | ∀ X : fieldFixed n, e X.val = X.val}
  one_mem' := by intro X; rfl
  mul_mem' := by
    intro e f he hf X
    change e (f X.val) = X.val
    rw [hf, he]
  inv_mem' := by
    intro e he X
    apply e.injective
    change e (e.symm X.val) = e X.val
    rw [LinearEquiv.apply_symm_apply, he]

theorem fieldSwapBinary_mem_pointwiseFixed : fieldSwapBinary n ∈ pointwiseFixed n := by
  intro X
  exact (mem_fieldFixed n X.val).mp X.property

/-- Automorphisms of the quadratic extension fixing F are identity or σ. -/
theorem coefficient_eq_one_or_sigma (τ : E n ≃+* E n)
    (hτ : ∀ c : F n, τ c.val = c.val) : τ = 1 ∨ τ = sigma n := by
  classical
  let t : E n ≃ₐ[F n] E n := AlgEquiv.ofRingEquiv (f := τ) hτ
  have hs : (sigmaAlg n : E n ≃ₐ[F n] E n) ≠ 1 := by
    intro he
    obtain ⟨z, hz⟩ := exists_sigma_ne n
    exact hz (congrArg (fun a : E n ≃ₐ[F n] E n => a z) he)
  have ht : t = 1 ∨ t = sigmaAlg n := by
    by_contra! h
    have hcard := Finset.card_le_univ ({1, sigmaAlg n, t} : Finset (E n ≃ₐ[F n] E n))
    have hbound := AlgEquiv.card_le (F := F n) (K := E n)
    rw [finrank_E] at hbound
    have hthree : ({1, sigmaAlg n, t} : Finset (E n ≃ₐ[F n] E n)).card = 3 := by
      simp [Ne.symm hs, Ne.symm h.1, Ne.symm h.2]
    omega
  rcases ht with ht | ht
  · exact Or.inl (congrArg AlgEquiv.toRingEquiv ht)
  · exact Or.inr (congrArg AlgEquiv.toRingEquiv ht)

private theorem coefficient_fixed_of_pointwise (e : Space n ≃ₗ[ZMod 2] Space n)
    (he : e ∈ pointwiseFixed n)
    (A : Mat n) (τ : E n ≃+* E n)
    (hexpr : ∀ X : Space n, (e X).val = A * X.val.map τ * adjoint n A) :
    ∀ c : F n, τ c.val = c.val := by
  let D := diagonalUnit n 0
  have hmap : D.val.map τ = D.val := by
    ext i j
    simp [D, diagonalUnit, Matrix.single_apply, apply_ite]
  have hd : A * D.val * adjoint n A = D.val := by
    rw [← hmap, ← hexpr]
    simpa only [hmap] using congrArg Subtype.val (he ⟨D, diagonalUnit_mem_fixed n 0⟩)
  intro c
  have hmapc : (c • D).val.map τ = τ c.val • D.val := by
    ext i j
    change τ (c.val * D.val i j) = τ c.val * D.val i j
    rw [map_mul]
    exact congrArg (fun z => τ c.val * z) (congrArg (fun B : Mat n => B i j) hmap)
  have hcd : A * (c • D).val.map τ * adjoint n A = (c • D).val := by
    rw [← hexpr]
    exact congrArg Subtype.val
      (he ⟨c • D, (fieldFixed n).smul_mem c (diagonalUnit_mem_fixed n 0)⟩)
  rw [hmapc, Matrix.mul_smul, Matrix.smul_mul, hd] at hcd
  have h00 := congrArg (fun B : Mat n => B 0 0) hcd
  simpa [D, diagonalUnit, Matrix.single_apply, Subfield.smul_def] using h00

/-- Under coverage, fixing C_V(σ) leaves only identity and the marked swap. -/
theorem eq_one_or_fieldSwapBinary_of_fixes (hcov : NormalizerCoverage n)
    (e : Space n ≃ₗ[ZMod 2] Space n) (hen : e ∈ binaryNormalizer n)
    (he : ∀ X : fieldFixed n, e X.val = X.val) : e = 1 ∨ e = fieldSwapBinary n := by
  obtain ⟨g, τ, hexpr⟩ := hcov e hen
  have hτ := coefficient_fixed_of_pointwise n e he (g : Mat n) τ hexpr
  have hmap (X : Space n) (hX : X.val.transpose = X.val) : X.val.map τ = X.val := by
    have hmem : X ∈ fieldFixed n := (mem_fieldFixed n X).mpr (Subtype.ext hX)
    ext i j
    exact hτ ⟨X.val i j, fieldFixed_entry n ⟨X, hmem⟩ i j⟩
  have hg : ∀ X : Space n, X.val.transpose = X.val →
      (g : Mat n) * X.val * adjoint n (g : Mat n) = X.val := by
    intro X hX
    rw [← hmap X hX, ← hexpr]
    simpa only [hmap X hX] using congrArg Subtype.val
      (he ⟨X, (mem_fieldFixed n X).mpr (Subtype.ext hX)⟩)
  obtain ⟨c, hc, hnorm⟩ := eq_scalar_of_fixes_symmetric n (g : Mat n) hg
  have heτ (X : Space n) : (e X).val = X.val.map τ := by
    rw [hexpr, hc, scalar_action n c hnorm]
  rcases coefficient_eq_one_or_sigma n τ hτ with ht | ht
  · left
    apply LinearEquiv.ext
    intro X
    apply Subtype.ext
    simpa [ht] using heτ X
  · right
    apply LinearEquiv.ext
    intro X
    apply Subtype.ext
    change (e X).val = (fieldSwap n X).val
    rw [heτ, ht, fieldSwap_eq_map]

/-- The requested pointwise-fixing equivalence in the entire binary normalizer. -/
theorem fixes_iff_mem_zpowers (hcov : NormalizerCoverage n)
    (e : Space n ≃ₗ[ZMod 2] Space n) (hen : e ∈ binaryNormalizer n) :
    (∀ X : fieldFixed n, e X.val = X.val) ↔ e ∈ Subgroup.zpowers (fieldSwapBinary n) := by
  constructor
  · intro he
    rcases eq_one_or_fieldSwapBinary_of_fixes n hcov e hen he with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · intro he
    exact (Subgroup.zpowers_le.mpr (fieldSwapBinary_mem_pointwiseFixed n)) he

/-- The ambient image of the relative pointwise centralizer in a source overgroup. -/
theorem source_pointwiseFixed_eq (hcov : NormalizerCoverage n)
    (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : SourceOvergroup n M)
    (hs : fieldSwapBinary n ∈ M) :
    M ⊓ pointwiseFixed n = Subgroup.zpowers (fieldSwapBinary n) := by
  apply le_antisymm
  · intro e he
    exact (fixes_iff_mem_zpowers n hcov e (sourceOvergroup_le_normalizer n M hM he.1)).mp he.2
  · exact le_inf (Subgroup.zpowers_le.mpr hs)
      (Subgroup.zpowers_le.mpr (fieldSwapBinary_mem_pointwiseFixed n))

/-- The pointwise centralizer as an actual subgroup of M. -/
theorem source_relative_pointwiseFixed_eq (hcov : NormalizerCoverage n)
    (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : SourceOvergroup n M)
    (hs : fieldSwapBinary n ∈ M) :
    (pointwiseFixed n).comap M.subtype = Subgroup.zpowers (⟨fieldSwapBinary n, hs⟩ : M) := by
  apply le_antisymm
  · intro e he
    rcases eq_one_or_fieldSwapBinary_of_fixes n hcov e.val
      (sourceOvergroup_le_normalizer n M hM e.property) he with h | h
    · have he1 : e = 1 := Subtype.ext h
      rw [he1]
      exact Subgroup.one_mem _
    · have hes : e = ⟨fieldSwapBinary n, hs⟩ := Subtype.ext h
      rw [hes]
      exact Subgroup.mem_zpowers _
  · apply Subgroup.zpowers_le.mpr
    exact fieldSwapBinary_mem_pointwiseFixed n

end Representation.HermitianTensorThree.ImageOuter.FieldSections
