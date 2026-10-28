module

public import Theory.Representation.SL2.BinarySmallModels
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Basic
public import Theory.SpecificGroups.PSL2.InvolutionFusion
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Involution displacement on the binary SL₂(8) triple tensor

Every involution on the genuine model `N ⊗ N^σ ⊗ N^(σ²)` has displacement
rank at least three over GF(8). For the upper unipotent matrix with parameter
one, the Frobenius twists fix its entries. The displacements of the tensor
basis vectors `100`, `110`, and `101` are respectively `000`,
`000 + 100 + 010`, and `000 + 100 + 001`. Their coordinates prove independence.

The canonical characteristic-two SL₂/PSL₂ isomorphism lifts involution fusion
from the actual central quotient. The representation of a conjugating element
then identifies the displacement spaces, completing the bound for every
involution without a conjugacy or rank premise.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.9.3(16),
printed pp.354–357, and the exclusion in 15.3.58, printed p.1149.
-/

open scoped MatrixGroups TensorProduct
open Representation Representation.SL2.BinarySmall
open Module

noncomputable section
namespace Representation.SL2.BinarySmall.TripleInvolution

private lemma rank_ge_of_independent {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (P : Submodule k V) (v : Fin 3 → V) (hi : LinearIndependent k v)
    (hm : ∀ i, v i ∈ P) : 3 ≤ finrank k P := by
  let w : Fin 3 → P := fun i => ⟨v i, hm i⟩
  have hw : LinearIndependent k w := LinearIndependent.of_comp P.subtype hi
  exact hw.fintype_card_le_finrank

private lemma finrank_movedSpace_conj {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (a c : G) :
    finrank k (RankTwo.movedSpace ρ a) =
      finrank k (RankTwo.movedSpace ρ (c * a * c⁻¹)) := by
  let f : V ≃ₗ[k] V :=
    { toLinearMap := ρ c
      invFun := ρ c⁻¹
      left_inv := ρ.inv_self_apply c
      right_inv := ρ.self_inv_apply c }
  exact RankTwo.finrank_movedSpace_transport ρ ρ (MulAut.conj c) f
    (by
      intro h z
      change ρ c (ρ h z) = ρ (c * h * c⁻¹) (ρ c z)
      simp only [map_mul, Module.End.mul_apply, Representation.inv_self_apply]) a

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

private def unipotent : SL(2,K) := ⟨!![1,1;0,1], by simp⟩

private def naturalBasis : Basis (Fin 2) K (NaturalSpace K) := Pi.basisFun K (Fin 2)

private def tensorBasis : Basis ((Fin 2 × Fin 2) × Fin 2) K (TripleSpace K) :=
  ((naturalBasis (K := K)).tensorProduct naturalBasis).tensorProduct naturalBasis

private lemma twist_basis_zero (j : ℕ) :
    frobeniusNatural j (unipotent (K := K)) (naturalBasis 0) = naturalBasis 0 := by
  rw [frobeniusNatural_apply]
  ext i
  fin_cases i <;> simp [unipotent, naturalBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma twist_basis_one (j : ℕ) :
    frobeniusNatural j (unipotent (K := K)) (naturalBasis 1) =
      naturalBasis 0 + naturalBasis 1 := by
  rw [frobeniusNatural_apply]
  ext i
  fin_cases i <;> simp [unipotent, naturalBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

omit [Finite K] in
private lemma unipotent_order : orderOf (unipotent (K := K)) = 2 := by
  apply (orderOf_eq_prime_iff (p := 2)).mpr
  constructor
  · rw [pow_two]
    apply Subtype.ext
    change (unipotent (K := K)).val * (unipotent (K := K)).val = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unipotent, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  · intro h
    have := congrArg (fun x : SL(2,K) => x.val 0 1) h
    simp [unipotent] at this

private lemma displacement100 :
    triple (unipotent (K := K)) (tensorBasis ((1,0),0)) - tensorBasis ((1,0),0) =
      tensorBasis ((0,0),0) := by
  simp only [tensorBasis, Basis.tensorProduct_apply, triple_apply_tmul,
    twist_basis_zero, twist_basis_one, TensorProduct.add_tmul]
  abel

private lemma displacement110 :
    triple (unipotent (K := K)) (tensorBasis ((1,1),0)) - tensorBasis ((1,1),0) =
      tensorBasis ((0,0),0) + tensorBasis ((1,0),0) + tensorBasis ((0,1),0) := by
  simp only [tensorBasis, Basis.tensorProduct_apply, triple_apply_tmul,
    twist_basis_zero, twist_basis_one, TensorProduct.add_tmul, TensorProduct.tmul_add]
  abel

private lemma displacement101 :
    triple (unipotent (K := K)) (tensorBasis ((1,0),1)) - tensorBasis ((1,0),1) =
      tensorBasis ((0,0),0) + tensorBasis ((1,0),0) + tensorBasis ((0,0),1) := by
  simp only [tensorBasis, Basis.tensorProduct_apply, triple_apply_tmul,
    twist_basis_zero, twist_basis_one, TensorProduct.add_tmul, TensorProduct.tmul_add]
  abel

private def displacementVectors : Fin 3 → TripleSpace K :=
  ![tensorBasis ((0,0),0), tensorBasis ((0,0),0) + tensorBasis ((1,0),0) + tensorBasis ((0,1),0),
    tensorBasis ((0,0),0) + tensorBasis ((1,0),0) + tensorBasis ((0,0),1)]

omit [Finite K] [CharP K 2] in
private lemma displacementVectors_independent :
    LinearIndependent K (displacementVectors (K := K)) := by
  apply (Fintype.linearIndependent_iff (R := K) (v := displacementVectors (K := K))).mpr
  intro a ha i
  simp only [Fin.sum_univ_three, displacementVectors, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] at ha
  have h1 := congrArg ((tensorBasis (K := K)).coord ((0,1),0)) ha
  have h2 := congrArg ((tensorBasis (K := K)).coord ((0,0),1)) ha
  have h0 := congrArg ((tensorBasis (K := K)).coord ((0,0),0)) ha
  simp only [map_add, map_smul, map_zero, Basis.coord_apply, Basis.repr_self_apply,
    smul_eq_mul] at h1 h2 h0
  norm_num at h1 h2 h0
  fin_cases i <;> simp_all

private lemma displacementVectors_mem (i : Fin 3) :
    displacementVectors (K := K) i ∈
      RankTwo.movedSpace (k := K) (V := TripleSpace K) (triple (K := K)) unipotent := by
  fin_cases i
  · exact ⟨tensorBasis ((1,0),0), displacement100⟩
  · exact ⟨tensorBasis ((1,1),0), displacement110⟩
  · exact ⟨tensorBasis ((1,0),1), displacement101⟩

private lemma unipotent_rank_ge :
    3 ≤ finrank K (RankTwo.movedSpace (k := K) (V := TripleSpace K)
      (triple (K := K)) (unipotent (K := K))) := by
  exact rank_ge_of_independent (k := K) (V := TripleSpace K)
    (RankTwo.movedSpace (k := K) (V := TripleSpace K) (triple (K := K)) (unipotent (K := K)))
    (displacementVectors (K := K)) (displacementVectors_independent (K := K))
    (displacementVectors_mem (K := K))

/-- Every involution has displacement dimension at least three over the
field of eight elements on the actual three-factor Frobenius tensor. -/
public theorem rank_ge (g : SL(2,GaloisField 2 3)) (hg : orderOf g = 2) :
    3 ≤ Module.finrank (GaloisField 2 3)
      (RankTwo.movedSpace (k := GaloisField 2 3) (V := TripleSpace (GaloisField 2 3))
        (triple (K := GaloisField 2 3)) g) := by
  let e := Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)
  have hc : IsConj (unipotent (K := GaloisField 2 3)) g := by
    have hp := Theory.PSL2.involutions_isConj (e unipotent) (e g)
      ((e.orderOf_eq unipotent).trans unipotent_order) ((e.orderOf_eq g).trans hg)
    simpa only [MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using e.symm.toMonoidHom.map_isConj hp
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  rw [← hc, ← finrank_movedSpace_conj]
  exact unipotent_rank_ge

end Representation.SL2.BinarySmall.TripleInvolution
