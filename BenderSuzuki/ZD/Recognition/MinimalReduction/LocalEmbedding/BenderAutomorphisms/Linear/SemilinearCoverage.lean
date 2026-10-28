module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.FieldAction
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage.Multiplicativity
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage.Normalization

/-!
# Semilinear coverage for arbitrary automorphisms of binary PSL₂

The actual characteristic-two quotient equivalence transports an SL₂
factorization into an inner automorphism and an entrywise field automorphism
to the corresponding PSL₂ factorization. Sylow conjugacy and an explicit Borel
matrix normalize an arbitrary automorphism to preserve the upper root group and
fix the Weyl involution. Root-coordinate reconstruction then gives its field
automorphism. Both steps are proved in the imported modules.

The source theorem is GLS, Volume 4, Chapter 4, Lemma 3.1(a), also used in 3.4(c).
(In the source TeX, clause 3.1(b) instead concerns Suzuki groups.)
-/

namespace BenderSuzuki.ZD.Linear
open Converse _root_.BenderSuzuki.MatrixGroups

variable {K : Type*} [Field K] [CharP K 2]

public theorem quotient_congr_conj (g : SL2 K) :
    MulAut.congr (sl2QuotientEquiv K) (MulAut.conj g) =
      MulAut.conj (Converse.pi K g) := by
  ext x
  obtain ⟨y, rfl⟩ := Converse.pi_surjective x
  change sl2QuotientEquiv K
    (g * (sl2QuotientEquiv K).symm (sl2QuotientEquiv K y) * g⁻¹) =
      Converse.pi K g * Converse.pi K y * (Converse.pi K g)⁻¹
  rw [MulEquiv.symm_apply_apply, map_mul, map_mul, map_inv]
  rfl

/-- The matrix factorization descends through the actual SL₂–PSL₂ quotient. -/
public theorem semilinear_of_lift_factorization (a : MulAut (PSL2MatrixGroup K))
    (g : SL2 K) (σ : K ≃+* K)
    (ha : (MulAut.congr (sl2QuotientEquiv K)).symm a = MulAut.conj g * sl2FieldAut σ) :
    a = MulAut.conj (Converse.pi K g) * fieldAut σ := by
  have h := congrArg (MulAut.congr (sl2QuotientEquiv K)) ha
  rw [MulEquiv.apply_symm_apply, map_mul, quotient_congr_conj] at h
  exact h

/-- Conditional assembly from inner normalization and root-coordinate
multiplicativity, also available independently of the finite-field proofs. -/
public theorem semilinear_of_root_reductions
    (normalize : ∀ a : MulAut (SL2 K), ∃ (g : SL2 K) (b : MulAut (SL2 K)),
      a = MulAut.conj g * b ∧ (Unip K).map b.toMonoidHom = Unip K ∧
        b (weyl K) = weyl K)
    (multiply : ∀ b : MulAut (SL2 K),
      (Unip K).map b.toMonoidHom = Unip K → b (weyl K) = weyl K →
      ∀ s t : K, rootParameter b (s * t) = rootParameter b s * rootParameter b t)
    (a : MulAut (PSL2MatrixGroup K)) :
    ∃ (g : PSL2MatrixGroup K) (σ : K ≃+* K), a = MulAut.conj g * fieldAut σ := by
  obtain ⟨g, b, hab, hU, hw⟩ := normalize ((MulAut.congr (sl2QuotientEquiv K)).symm a)
  obtain ⟨σ, hσ⟩ := eq_sl2FieldAut_of_rootParameter_mul b hU hw (multiply b hU hw)
  exact ⟨Converse.pi K g, σ, semilinear_of_lift_factorization a g σ (hσ ▸ hab)⟩

/-- Every abstract automorphism of PSL₂ over a finite field of characteristic two
is inner times the actual entrywise field automorphism. -/
public theorem semilinear_coverage [Finite K] (a : MulAut (PSL2MatrixGroup K)) :
    ∃ (g : PSL2MatrixGroup K) (σ : K ≃+* K), a = MulAut.conj g * fieldAut σ :=
  semilinear_of_root_reductions exists_root_weyl_normalization rootParameter_mul a

/-- The binary models with `n ≥ 2`, including PSL₂(4), satisfy semilinear coverage. -/
public theorem binary_semilinear_coverage {n : ℕ} (_hn : 2 ≤ n)
    (a : MulAut (PSL2BinaryMatrixGroup n)) :
    ∃ (g : PSL2BinaryMatrixGroup n)
      (σ : PFAppendixIII.BinaryGaloisField n ≃+* PFAppendixIII.BinaryGaloisField n),
      a = MulAut.conj g * fieldAut σ :=
  semilinear_coverage a

end BenderSuzuki.ZD.Linear
