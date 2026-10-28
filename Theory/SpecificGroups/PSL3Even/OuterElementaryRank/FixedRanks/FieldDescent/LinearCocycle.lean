module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Quadratic matrix Hilbert–90 in dimension three

Invariant vectors of a semilinear involution span the ambient space: a linear
form annihilating them annihilates every `v + T(v)`, contradicting Artin's
independence of the identity and the nontrivial coefficient involution.
Choosing an invariant basis gives `A * σ(P) = P`. This works also in
characteristic two and uses no division by the order of the automorphism.

Adapted from the project's checked cubic argument in
`PSL3.StandardCubicFixedNine.Descent.LinearCocycle`. Source context: GLS3,
Theorem 2.5.12 and §2.7; Aschbacher–Smith 16.1.4(4), printed p.1171.
-/

public section

open Matrix Module
namespace Matrix.PSL3Even.OuterElementaryRank.FixedRanks.FieldDescent
variable {F : Type*} [Field F]

private theorem quadratic_fixed_span {V : Type*} [AddCommGroup V] [Module F V]
    (σ : F ≃+* F) (hs : orderOf σ = 2) (T : V →+ V)
    (hsemi : ∀ (a : F) v, T (a • v) = σ a • T v)
    (hT : ∀ v, T (T v) = v) :
    Submodule.span F {v : V | T v = v} = ⊤ := by
  classical
  let W := Submodule.span F {v : V | T v = v}
  by_contra hn
  obtain ⟨φ, hφ, hW⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (show W < ⊤ from lt_top_iff_ne_top.mpr hn) inferInstance
  have hsum (a : F) (v : V) : a • v + T (a • v) ∈ W := by
    apply Submodule.subset_span
    change T (a • v + T (a • v)) = _
    simp only [map_add, hT]
    abel
  have hi : LinearIndependent F (fun i : Fin 2 => fun a : F => (σ ^ i.val) a) := by
    apply (linearIndependent_monoidHom F F).comp
      (fun i : Fin 2 => (σ ^ i.val).toMonoidHom)
    intro i j he
    apply Fin.ext
    apply pow_injOn_Iio_orderOf (x := σ) (by simpa only [hs, Set.mem_Iio] using i.isLt)
      (by simpa only [hs, Set.mem_Iio] using j.isLt)
    ext a
    exact DFunLike.congr_fun he a
  apply hφ
  ext v
  let w : Fin 2 → V := ![v, T v]
  have hz : ∑ i : Fin 2, φ (w i) • (fun a : F => (σ ^ i.val) a) = 0 := by
    ext a
    have hm : φ (a • v + T (a • v)) = 0 := by
      have := Submodule.mem_map_of_mem (hsum a v) (f := φ)
      rwa [hW, Submodule.mem_bot] at this
    simpa [Fin.sum_univ_succ, w, hsemi, map_add, map_smul, mul_comm,
      pow_succ, add_assoc] using hm
  have hh := linearIndependent_iff'.mp hi Finset.univ (fun i => φ (w i)) hz 0
    (Finset.mem_univ 0)
  exact hh

/-- A genuine quadratic matrix cocycle has an invertible descent basis. -/
theorem linear_cocycle_descent (σ : F ≃+* F) (hs : orderOf σ = 2)
    (A : GL (Fin 3) F)
    (hA : A * GeneralLinearGroup.map σ.toRingHom A = 1) :
    ∃ P : GL (Fin 3) F, A * GeneralLinearGroup.map σ.toRingHom P = P := by
  classical
  let T : (Fin 3 → F) →+ (Fin 3 → F) :=
    { toFun := fun v => A.val *ᵥ (σ ∘ v)
      map_zero' := by
        simp only [Function.comp_def, Pi.zero_apply, map_zero]
        exact Matrix.mulVec_zero A.val
      map_add' := fun v w => by
        simp only [Function.comp_def, Pi.add_apply, map_add]
        exact Matrix.mulVec_add _ _ _ }
  have hsemi (a : F) (v : Fin 3 → F) : T (a • v) = σ a • T v := by
    change A.val *ᵥ (σ ∘ (a • v)) = σ a • (A.val *ᵥ (σ ∘ v))
    rw [← Matrix.mulVec_smul]
    congr 1
    ext i
    exact map_mul σ a (v i)
  have hmap (B : Matrix (Fin 3) (Fin 3) F) (v : Fin 3 → F) :
      σ ∘ (B *ᵥ v) = B.map σ *ᵥ (σ ∘ v) := by
    ext i
    exact RingHom.map_mulVec σ.toRingHom B v i
  have hT (v : Fin 3 → F) : T (T v) = v := by
    change A.val *ᵥ (σ ∘ (A.val *ᵥ (σ ∘ v))) = v
    rw [hmap, Matrix.mulVec_mulVec]
    have hm := congrArg Units.val hA
    change A.val * A.val.map σ = 1 at hm
    rw [hm, Matrix.one_mulVec]
    ext i
    exact DFunLike.congr_fun ((orderOf_eq_prime_iff.mp hs).1) (v i)
  have hspan := quadratic_fixed_span σ hs T hsemi hT
  let s : Set (Fin 3 → F) := {v | T v = v}
  have hsp : ⊤ ≤ Submodule.span F s := le_of_eq hspan.symm
  obtain ⟨s', b, hb⟩ : ∃ (s' : Set (Fin 3 → F)) (b : Basis s' F (Fin 3 → F)),
      ∀ i, T (b i) = b i := by
    exact ⟨_, Basis.ofSpan hsp, fun i => Basis.ofSpan_subset hsp (Set.mem_range_self i)⟩
  let : Finite s' := Module.Finite.finite_basis b
  let : Fintype s' := Fintype.ofFinite s'
  have hc : Fintype.card s' = Fintype.card (Fin 3) := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_pi]
  let e := Fintype.equivOfCardEq hc
  let b' := b.reindex e
  let b₀ := Pi.basisFun F (Fin 3)
  let P : GL (Fin 3) F :=
    { val := b₀.toMatrix b'
      inv := b'.toMatrix b₀
      val_inv := Basis.toMatrix_mul_toMatrix_flip _ _
      inv_val := Basis.toMatrix_mul_toMatrix_flip _ _ }
  refine ⟨P, ?_⟩
  apply Units.ext
  ext i j
  have hj := congrFun (hb (e.symm j)) i
  simpa [P, b₀, Basis.toMatrix_apply, Pi.basisFun_repr, b', Basis.reindex_apply,
    T, Matrix.mul_apply, Matrix.mulVec, dotProduct] using hj

end Matrix.PSL3Even.OuterElementaryRank.FixedRanks.FieldDescent
