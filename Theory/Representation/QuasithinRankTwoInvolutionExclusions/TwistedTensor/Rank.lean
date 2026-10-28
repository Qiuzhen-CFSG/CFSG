module

public import Theory.Representation.SL2.BinarySmallModels
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Basic
public import Theory.SpecificGroups.PSL2.InvolutionFusion
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Exact displacement rank on a twisted triple tensor

For a finite field of characteristic two and a specified field automorphism σ,
every nonidentity involution of SL₂ has displacement rank four on
`N ⊗ N^σ ⊗ N^(σ²)`. The upper unipotent with parameter one is fixed by every
coefficient twist. The displacements of tensor-basis vectors 100, 110, 101 and
111 are independent. The displacement squares to zero, so rank-nullity gives
the matching upper bound in dimension eight. Genuine SL₂/PSL₂ involution fusion
and an intertwining conjugation then give the result for every involution.

The explicit Frobenius comparison identifies this action with the existing
`Representation.SL2.BinarySmall.triple` model. The basis calculation extends
`Theory.Representation.SL2.BinarySmallInvolution.Triple` without changing that
shared module or assuming its numerical conclusion.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, G.11.2(11),
printed p.364 (PDF p.375), and the proof of 6.2.19, printed p.691 (PDF p.708).
-/

open scoped MatrixGroups TensorProduct
open Representation Representation.SL2.BinarySmall
open Module

@[expose] public noncomputable section
namespace Representation.RankTwo.TwistedTensor

private lemma rank_ge_of_independent {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (P : Submodule k V) (v : Fin 4 → V) (hi : LinearIndependent k v)
    (hm : ∀ i, v i ∈ P) : 4 ≤ finrank k P := by
  let w : Fin 4 → P := fun i => ⟨v i, hm i⟩
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

private lemma involution_rank_le_half {k G V : Type*} [Field k] [CharP k 2]
    [Group G] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (g : G) (hsq : g * g = 1) :
    2 * finrank k (movedSpace ρ g) ≤ finrank k V := by
  let f : Module.End k V := ρ g - 1
  have hle : LinearMap.range f ≤ LinearMap.ker f := by
    rintro _ ⟨z, rfl⟩
    change ρ g (ρ g z - z) - (ρ g z - z) = 0
    rw [map_sub, ← Module.End.mul_apply, ← map_mul, hsq, map_one,
      Module.End.one_apply]
    have hneg (v : V) : -v = v := by
      rw [← neg_one_smul k, CharTwo.neg_eq (1 : k), one_smul]
    simp only [sub_eq_add_neg, hneg]
    rw [add_comm z (ρ g z), ← two_smul k, CharTwo.two_eq_zero, zero_smul]
  have hle' := Submodule.finrank_mono hle
  have he := LinearMap.finrank_range_add_finrank_ker f
  change 2 * finrank k (LinearMap.range f) ≤ finrank k V
  omega

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

/-- The natural matrix action after applying the specified field automorphism. -/
def twistedNatural (σ : K ≃+* K) : Representation K SL(2,K) (NaturalSpace K) :=
  (specialLinearNatural 2).comp (Matrix.SpecialLinearGroup.map σ.toRingHom)

/-- The literal three-factor tensor for the specified field automorphism. -/
def twistedTriple (σ : K ≃+* K) : Representation K SL(2,K) (TripleSpace K) :=
  ((twistedNatural 1).tprod (twistedNatural σ)).tprod (twistedNatural (σ ^ 2))

omit [Finite K] [CharP K 2] in
lemma twistedTriple_apply_tmul (σ : K ≃+* K) (g : SL(2,K)) (u v w : NaturalSpace K) :
    twistedTriple σ g ((u ⊗ₜ[K] v) ⊗ₜ[K] w) =
      ((twistedNatural 1 g u) ⊗ₜ[K] (twistedNatural σ g v)) ⊗ₜ[K]
        (twistedNatural (σ ^ 2) g w) := by
  simp only [twistedTriple, Representation.tprod_apply, TensorProduct.map_tmul]

/-- The standard Frobenius choice is the pre-existing binary triple model. -/
lemma twistedTriple_frobenius :
    twistedTriple (frobeniusEquiv K 2) = (triple (K := K)) := by
  simp only [twistedTriple, twistedNatural, triple, frobeniusNatural,
    iterateFrobeniusEquiv_eq_pow, pow_zero, pow_one]

private def unipotent : SL(2,K) := ⟨!![1,1;0,1], by simp⟩

private def naturalBasis : Basis (Fin 2) K (NaturalSpace K) := Pi.basisFun K (Fin 2)

private def tensorBasis : Basis ((Fin 2 × Fin 2) × Fin 2) K (TripleSpace K) :=
  ((naturalBasis (K := K)).tensorProduct naturalBasis).tensorProduct naturalBasis

omit [Finite K] [CharP K 2] in
private lemma twist_basis_zero (τ : K ≃+* K) :
    twistedNatural τ (unipotent (K := K)) (naturalBasis 0) = naturalBasis 0 := by
  change Matrix.mulVec ((unipotent (K := K)).val.map τ) _ = _
  ext i
  fin_cases i <;> simp [unipotent, naturalBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

omit [Finite K] [CharP K 2] in
private lemma twist_basis_one (τ : K ≃+* K) :
    twistedNatural τ (unipotent (K := K)) (naturalBasis 1) =
      naturalBasis 0 + naturalBasis 1 := by
  change Matrix.mulVec ((unipotent (K := K)).val.map τ) _ = _
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

variable (σ : K ≃+* K)

omit [Finite K] [CharP K 2] in
private lemma displacement100 :
    twistedTriple σ (unipotent (K := K)) (tensorBasis ((1,0),0)) - tensorBasis ((1,0),0) =
      tensorBasis ((0,0),0) := by
  simp only [tensorBasis, Basis.tensorProduct_apply, twistedTriple_apply_tmul,
    twist_basis_zero, twist_basis_one, TensorProduct.add_tmul]
  abel

omit [Finite K] [CharP K 2] in
private lemma displacement110 :
    twistedTriple σ (unipotent (K := K)) (tensorBasis ((1,1),0)) - tensorBasis ((1,1),0) =
      tensorBasis ((0,0),0) + tensorBasis ((1,0),0) + tensorBasis ((0,1),0) := by
  simp only [tensorBasis, Basis.tensorProduct_apply, twistedTriple_apply_tmul,
    twist_basis_zero, twist_basis_one, TensorProduct.add_tmul, TensorProduct.tmul_add]
  abel

omit [Finite K] [CharP K 2] in
private lemma displacement101 :
    twistedTriple σ (unipotent (K := K)) (tensorBasis ((1,0),1)) - tensorBasis ((1,0),1) =
      tensorBasis ((0,0),0) + tensorBasis ((1,0),0) + tensorBasis ((0,0),1) := by
  simp only [tensorBasis, Basis.tensorProduct_apply, twistedTriple_apply_tmul,
    twist_basis_zero, twist_basis_one, TensorProduct.add_tmul, TensorProduct.tmul_add]
  abel

omit [Finite K] [CharP K 2] in
private lemma displacement111 :
    twistedTriple σ (unipotent (K := K)) (tensorBasis ((1,1),1)) - tensorBasis ((1,1),1) =
      tensorBasis ((0,0),0) + tensorBasis ((1,0),0) + tensorBasis ((0,1),0) +
      tensorBasis ((0,0),1) + tensorBasis ((1,1),0) + tensorBasis ((1,0),1) +
      tensorBasis ((0,1),1) := by
  simp only [tensorBasis, Basis.tensorProduct_apply, twistedTriple_apply_tmul,
    twist_basis_one, TensorProduct.add_tmul, TensorProduct.tmul_add]
  abel

private def displacementVectors : Fin 4 → TripleSpace K :=
  ![tensorBasis ((0,0),0), tensorBasis ((0,0),0) + tensorBasis ((1,0),0) + tensorBasis ((0,1),0),
    tensorBasis ((0,0),0) + tensorBasis ((1,0),0) + tensorBasis ((0,0),1),
    tensorBasis ((0,0),0) + tensorBasis ((1,0),0) + tensorBasis ((0,1),0) +
      tensorBasis ((0,0),1) + tensorBasis ((1,1),0) + tensorBasis ((1,0),1) +
      tensorBasis ((0,1),1)]

omit [Finite K] [CharP K 2] in
private lemma displacementVectors_independent :
    LinearIndependent K (displacementVectors (K := K)) := by
  apply (Fintype.linearIndependent_iff (R := K) (v := displacementVectors (K := K))).mpr
  intro a ha i
  simp only [Fin.sum_univ_four, displacementVectors, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three] at ha
  have h3 := congrArg ((tensorBasis (K := K)).coord ((1,1),0)) ha
  have h1 := congrArg ((tensorBasis (K := K)).coord ((0,1),0)) ha
  have h2 := congrArg ((tensorBasis (K := K)).coord ((0,0),1)) ha
  have h0 := congrArg ((tensorBasis (K := K)).coord ((0,0),0)) ha
  simp only [map_add, map_smul, map_zero, Basis.coord_apply, Basis.repr_self_apply,
    smul_eq_mul] at h1 h2 h0 h3
  norm_num at h1 h2 h0 h3
  fin_cases i <;> simp_all

omit [Finite K] [CharP K 2] in
private lemma displacementVectors_mem (i : Fin 4) :
    displacementVectors (K := K) i ∈
      RankTwo.movedSpace (k := K) (V := TripleSpace K) (twistedTriple σ) unipotent := by
  fin_cases i
  · exact ⟨tensorBasis ((1,0),0), displacement100 σ⟩
  · exact ⟨tensorBasis ((1,1),0), displacement110 σ⟩
  · exact ⟨tensorBasis ((1,0),1), displacement101 σ⟩
  · exact ⟨tensorBasis ((1,1),1), displacement111 σ⟩

omit [Finite K] [CharP K 2] in
private lemma unipotent_rank_ge :
    4 ≤ finrank K (RankTwo.movedSpace (k := K) (V := TripleSpace K)
      (twistedTriple σ) (unipotent (K := K))) := by
  exact rank_ge_of_independent (k := K) (V := TripleSpace K)
    (RankTwo.movedSpace (k := K) (V := TripleSpace K) (twistedTriple σ) (unipotent (K := K)))
    (displacementVectors (K := K)) (displacementVectors_independent (K := K))
    (displacementVectors_mem (K := K) σ)

set_option backward.isDefEq.respectTransparency false in
/-- Every nonidentity involution has displacement rank four on the actual
three-factor tensor with the specified twists. -/
theorem twisted_rank_eq_four (g : SL(2,K)) (hg : orderOf g = 2) :
    finrank K (movedSpace (k := K) (V := TripleSpace K) (twistedTriple σ) g) = 4 := by
  let e := Theory.PSL2.sl2QuotientEquiv K
  have hc : IsConj (unipotent (K := K)) g := by
    have hp := Theory.PSL2.involutions_isConj (e unipotent) (e g)
      ((e.orderOf_eq unipotent).trans unipotent_order) ((e.orderOf_eq g).trans hg)
    simpa only [MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using e.symm.toMonoidHom.map_isConj hp
  have hlo : 4 ≤ finrank K (movedSpace (k := K) (V := TripleSpace K) (twistedTriple σ) g) := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hc
    rw [← hc, ← finrank_movedSpace_conj]
    exact unipotent_rank_ge σ
  have hsq : g * g = 1 := by simpa only [hg, pow_two] using pow_orderOf_eq_one g
  have hhi := involution_rank_le_half (k := K) (V := TripleSpace K) (twistedTriple σ) g hsq
  have hdim : finrank K (TripleSpace K) = 8 := by
    simp [TripleSpace, NaturalSpace, Module.finrank_tensorProduct]
  omega

/-- Application to the canonical model with exponents 1, 2 and 4. -/
theorem rank_eq_four (g : SL(2,K)) (hg : orderOf g = 2) :
    finrank K (movedSpace (k := K) (V := TripleSpace K) triple g) = 4 := by
  rw [← twistedTriple_frobenius]
  exact twisted_rank_eq_four (frobeniusEquiv K 2) g hg

end Representation.RankTwo.TwistedTensor
