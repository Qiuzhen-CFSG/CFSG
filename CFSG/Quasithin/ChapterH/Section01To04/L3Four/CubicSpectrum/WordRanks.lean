module

public import CFSG.Quasithin.ChapterH.Section01To04.L3Four.CubicSpectrum.Definitions
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.TensorProduct.Basis
/-!
# Displacement ranks of the three adjoint words in H.4.7

Given eigenbases of the adjoint factors at the first two Frobenius embeddings,
the literal tensor words have displacement ranks six, six and forty-two.
The tensor basis includes the final trivial scalar factor in `wordRep`.
Its eigenvalues are powers of a primitive cube root, so displacement rank
counts precisely the exponents not divisible by three. The adjoint exponent
multiplicities are 2, 3, 3, and their tensor convolution gives 22, 21, 21.

The combined theorem supplies exactly the three absolute ranks requested by
`CubicSpectrum.Reduction.binary_displacement_of_word_ranks`. Existence of the
two adjoint eigenbases remains an explicit input to this conditional result.

Source: Aschbacher–Smith H.4.7, refs/quasithin.pdf, printed pp.382–383.
-/

public section

open scoped MatrixGroups TensorProduct
open Representation.SL3.BinaryDefiningFactors
namespace CFSG.Quasithin.ChapterH.Section01To04.L3Four.CubicSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {F K : Type*} [Field F] [Field K]
/-- In a cubic eigenbasis, displacement rank counts the nonfixed coordinates. -/
private theorem rank_eigenbasis {I V : Type*} [Fintype I] [AddCommGroup V] [Module K V]
    (b : Module.Basis I K V) (f : Module.End K V) (ω : K) (hω : orderOf ω = 3)
    (e : I → ℕ) (h : ∀ i, f (b i) = ω ^ e i • b i) :
    Module.finrank K (LinearMap.range (f - 1)) =
      Fintype.card {i : I // e i % 3 ≠ 0} := by
  classical
  have hmat : LinearMap.toMatrix b b (f - 1) =
      Matrix.diagonal (fun i => ω ^ e i - 1) := by
    ext i j
    simp only [LinearMap.toMatrix_apply, LinearMap.sub_apply, Module.End.one_apply,
      h, map_sub, map_smul, Module.Basis.repr_self, Finsupp.sub_apply,
      Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  have hr := Matrix.rank_eq_finrank_range_toLin (LinearMap.toMatrix b b (f - 1)) b b
  rw [Matrix.toLin_toMatrix, hmat, Matrix.rank_diagonal] at hr
  rw [← hr]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun i => by
    rw [sub_ne_zero, ne_eq, ← orderOf_dvd_iff_pow_eq_one, hω, Nat.dvd_iff_mod_eq_zero])

/-- The adjoint basis has eigenvalue multiplicities two, three and three. -/
theorem adjointCubicExponent_multiplicities : Fintype.card {i : Fin 8 // adjointCubicExponent i % 3 = 0} = 2 ∧
    Fintype.card {i : Fin 8 // adjointCubicExponent i % 3 = 1} = 3 ∧
    Fintype.card {i : Fin 8 // adjointCubicExponent i % 3 = 2} = 3 := by decide

/-- Tensoring two adjoint spectra gives multiplicities twenty-two, twenty-one
and twenty-one, with exponents read modulo three. -/
theorem adjointCubicTensorExponent_multiplicities : Fintype.card {i : Fin 8 × Fin 8 //
      (adjointCubicExponent i.1 + adjointCubicExponent i.2) % 3 = 0} = 22 ∧
    Fintype.card {i : Fin 8 × Fin 8 //
      (adjointCubicExponent i.1 + adjointCubicExponent i.2) % 3 = 1} = 21 ∧
    Fintype.card {i : Fin 8 × Fin 8 //
      (adjointCubicExponent i.1 + adjointCubicExponent i.2) % 3 = 2} = 21 := by decide

variable [CharP K 2]

/-- Diagonalize a literal two-letter word, including its final scalar factor. -/
private theorem word_pair_rank {I J : Type*} [Fintype I] [Fintype J]
    (ι : F →+* K) (g : SL(3,F)) (ω : K) (hω : orderOf ω = 3)
    (a b : Factor) (b0 : Module.Basis I K (Space K a))
    (b1 : Module.Basis J K (Space K b)) (e0 : I → ℕ) (e1 : J → ℕ)
    (h0 : ∀ i, factorRep ι a g (b0 i) = ω ^ e0 i • b0 i)
    (h1 : ∀ j, factorRep ((frobenius K 2).comp ι) b g (b1 j) = ω ^ e1 j • b1 j) :
    Module.finrank K (LinearMap.range (wordRep ι [a,b] g - 1)) =
      Fintype.card {i : I × J // (e0 i.1 + e1 i.2) % 3 ≠ 0} := by
  let B :=
    b0.tensorProduct (b1.tensorProduct (Module.Basis.singleton Unit K))
  have hB : ∀ i : I × (J × Unit), wordRep ι [a,b] g (B i) =
      ω ^ (e0 i.1 + e1 i.2.1) • B i := by
    rintro ⟨i,j,u⟩
    dsimp only [B]
    simp only [Module.Basis.tensorProduct_apply]
    change TensorProduct.map (factorRep ι a g)
      (TensorProduct.map (factorRep ((frobenius K 2).comp ι) b g)
        (1 : Module.End K K))
      (b0 i ⊗ₜ[K] (b1 j ⊗ₜ[K] (Module.Basis.singleton Unit K) u)) = _
    simp only [TensorProduct.map_tmul, h0, h1, Module.End.one_apply,
      pow_add, ← TensorProduct.smul_tmul', ← TensorProduct.tmul_smul, smul_smul]
  refine (rank_eigenbasis B _ ω hω _ hB).trans ?_
  exact Fintype.card_congr
    ((Equiv.prodCongr (Equiv.refl I) (Equiv.prodUnique J Unit)).subtypeEquiv
      (fun _ => Iff.rfl))

omit [CharP K 2] in
private theorem trivial_action (ι : F →+* K) (g : SL(3,F)) (ω : K) (i : Unit) :
    factorRep ι .trivial g ((Module.Basis.singleton Unit K) i) =
      ω ^ (0 : ℕ) • (Module.Basis.singleton Unit K) i := by
  simp only [pow_zero, one_smul]
  rfl

/-- The three absolute ranks consumed by H.4.7's binary displacement reduction.
The second eigenbasis is for the actual Frobenius-twisted embedding. -/
theorem word_ranks_of_adjointCubicEigenbases (ι : F →+* K) (g : SL(3,F))
    (ω : K) (hω : orderOf ω = 3) (D0 : AdjointCubicEigenbasis ι g ω)
    (D1 : AdjointCubicEigenbasis ((frobenius K 2).comp ι) g ω) :
    Module.finrank K (LinearMap.range (wordRep ι [.adjoint,.trivial] g - 1)) = 6 ∧
    Module.finrank K (LinearMap.range (wordRep ι [.trivial,.adjoint] g - 1)) = 6 ∧
    Module.finrank K (LinearMap.range (wordRep ι [.adjoint,.adjoint] g - 1)) = 42 := by
  have hadj : Fintype.card {i : Fin 8 // adjointCubicExponent i % 3 ≠ 0} = 6 := by
    rw [Fintype.card_subtype_compl, adjointCubicExponent_multiplicities.1]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [word_pair_rank ι g ω hω .adjoint .trivial D0.basis
      (Module.Basis.singleton Unit K) adjointCubicExponent (fun _ => 0)
      D0.action (trivial_action _ g ω)]
    exact (Fintype.card_congr ((Equiv.prodUnique (Fin 8) Unit).subtypeEquiv
      (fun i => by simp))).trans hadj
  · rw [word_pair_rank ι g ω hω .trivial .adjoint
      (Module.Basis.singleton Unit K) D1.basis (fun _ => 0) adjointCubicExponent
      (trivial_action _ g ω) D1.action]
    exact (Fintype.card_congr ((Equiv.uniqueProd (Fin 8) Unit).subtypeEquiv
      (fun i => by simp))).trans hadj
  · rw [word_pair_rank ι g ω hω .adjoint .adjoint D0.basis D1.basis
      adjointCubicExponent adjointCubicExponent D0.action D1.action,
      Fintype.card_subtype_compl, adjointCubicTensorExponent_multiplicities.1]
    rfl

end

end CFSG.Quasithin.ChapterH.Section01To04.L3Four.CubicSpectrum
