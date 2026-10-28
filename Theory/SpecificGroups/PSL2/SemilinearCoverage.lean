module

public import Theory.SpecificGroups.PSL2.SemilinearCoverage.Multiplicativity
public import Theory.SpecificGroups.PSL2.SemilinearCoverage.Normalization

/-!
# Every automorphism of binary PSL₂ is semilinear

Over a finite field of characteristic two, every abstract automorphism of SL₂
is inner times an entrywise field automorphism. Sylow conjugacy and a Borel
matrix normalize the upper root group and Weyl involution; the root parameters
then recover the field addition and multiplication. Transport along the actual
canonical quotient SL₂ → PSL₂ gives the same factorization in PSL₂.

This proves the coverage assertion used in the automorphism paragraph before
GLS2, Theorem 26.24, Step 5 (`refs/KGroup/GLS2/ChapterG.tex`). The field action
is exactly `Theory.PSL2.fieldAut` on the matrix quotient, with no semilinearity
hypothesis on the input automorphism. The general result also covers the field
of two elements; the final theorem specializes to the source's `n ≥ 2` models.

Adapted from
`BenderSuzuki/ZD/Recognition/MinimalReduction/LocalEmbedding/BenderAutomorphisms/Linear/SemilinearCoverage.lean`
and its descendants, which prove the same matrix argument for GLS4, Chapter 4,
Lemma 3.1(a). This extraction uses only Mathlib and Theory.
-/

namespace Theory.PSL2
open SemilinearCoverage

variable {K : Type*} [Field K] [CharP K 2]

/-- Every abstract automorphism of binary SL₂ is inner times the entrywise
action of a field automorphism. -/
public theorem sl2_semilinear_coverage [Finite K] (a : MulAut (SL2 K)) :
    ∃ (g : SL2 K) (σ : K ≃+* K), a = MulAut.conj g * sl2FieldAut σ := by
  obtain ⟨g, b, hab, hU, hw⟩ := exists_root_weyl_normalization a
  obtain ⟨σ, hσ⟩ := eq_sl2FieldAut_of_preserves_root_weyl b hU hw
  exact ⟨g, σ, hσ ▸ hab⟩

private theorem quotient_congr_conj (g : SL2 K) :
    MulAut.congr (sl2QuotientEquiv K) (MulAut.conj g) =
      MulAut.conj (quotientMap K g) := by
  ext x
  obtain ⟨y, rfl⟩ := quotientMap_surjective K x
  change sl2QuotientEquiv K
    (g * (sl2QuotientEquiv K).symm (sl2QuotientEquiv K y) * g⁻¹) =
      quotientMap K g * quotientMap K y * (quotientMap K g)⁻¹
  rw [MulEquiv.symm_apply_apply, map_mul, map_mul, map_inv]
  rfl

/-- Every abstract automorphism of PSL₂ over a finite field of characteristic
two is inner times the actual field action on the canonical matrix quotient. -/
public theorem semilinear_coverage [Finite K] (a : MulAut (Group K)) :
    ∃ (g : Group K) (σ : K ≃+* K), a = MulAut.conj g * fieldAut σ := by
  obtain ⟨g, σ, ha⟩ :=
    sl2_semilinear_coverage ((MulAut.congr (sl2QuotientEquiv K)).symm a)
  refine ⟨quotientMap K g, σ, ?_⟩
  have h := congrArg (MulAut.congr (sl2QuotientEquiv K)) ha
  rw [MulEquiv.apply_symm_apply, map_mul, quotient_congr_conj] at h
  exact h

/-- Arbitrary-automorphism coverage for the source models PSL₂(2ⁿ), `n ≥ 2`. -/
public theorem binary_semilinear_coverage {n : ℕ} (_hn : 2 ≤ n)
    (a : MulAut (BinaryGroup n)) :
    ∃ (g : BinaryGroup n) (σ : BinaryField n ≃+* BinaryField n),
      a = MulAut.conj g * fieldAut σ :=
  semilinear_coverage a

end Theory.PSL2
