module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Cubic matrix Hilbert–90 in dimension three

An invertible matrix with `A * σ(A) * σ²(A) = 1` defines a semilinear map
`T(v) = A * σ(v)` with cube one. Its invariant vectors span: a linear form
annihilating them annihilates every sum `v + T(v) + T²(v)`, contradicting
linear independence of the three field automorphisms. An invariant basis
therefore gives an invertible matrix `P` satisfying `A * σ(P) = P`.

The span argument specializes the checked finite-action argument in
`Theory.Representation.FiniteFieldSemilinearDisplacement.Descent` directly to
three iterates. It uses neither division by three nor a lower bound on the
field size. The conclusion holds over every field with an automorphism of
order three.

Source context: GLS3, Proposition 4.9.1(d), `refs/KGroup/GLS3/chapter4.tex`;
this supplies the matrix descent step used on the actual PSL₃ quotient.
-/

public section

open Matrix Module
namespace Matrix.PSL3.StandardCubicFixedNine.Descent
variable {F : Type*} [Field F]

private theorem cubic_fixed_span {V : Type*} [AddCommGroup V] [Module F V]
    (σ : F ≃+* F) (hs : orderOf σ = 3) (T : V →+ V)
    (hsemi : ∀ (a : F) v, T (a • v) = σ a • T v)
    (hT : ∀ v, T (T (T v)) = v) :
    Submodule.span F {v : V | T v = v} = ⊤ := by
  classical
  let W := Submodule.span F {v : V | T v = v}
  by_contra hn
  obtain ⟨φ, hφ, hW⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (show W < ⊤ from lt_top_iff_ne_top.mpr hn) inferInstance
  have hsum (a : F) (v : V) : a • v + T (a • v) + T (T (a • v)) ∈ W := by
    apply Submodule.subset_span
    change T (a • v + T (a • v) + T (T (a • v))) = _
    simp only [map_add, hT]
    abel
  have hi : LinearIndependent F (fun i : Fin 3 => fun a : F => (σ ^ i.val) a) := by
    apply (linearIndependent_monoidHom F F).comp
      (fun i : Fin 3 => (σ ^ i.val).toMonoidHom)
    intro i j he
    apply Fin.ext
    apply pow_injOn_Iio_orderOf (x := σ) (by simpa only [hs, Set.mem_Iio] using i.isLt)
      (by simpa only [hs, Set.mem_Iio] using j.isLt)
    ext a
    exact DFunLike.congr_fun he a
  apply hφ
  ext v
  let w : Fin 3 → V := ![v, T v, T (T v)]
  have hz : ∑ i : Fin 3, φ (w i) • (fun a : F => (σ ^ i.val) a) = 0 := by
    ext a
    have hm : φ (a • v + T (a • v) + T (T (a • v))) = 0 := by
      have := Submodule.mem_map_of_mem (hsum a v) (f := φ)
      rwa [hW, Submodule.mem_bot] at this
    simpa [Fin.sum_univ_succ, w, hsemi, map_add, map_smul, mul_comm,
      pow_succ, add_assoc] using hm
  have hh := linearIndependent_iff'.mp hi Finset.univ (fun i => φ (w i)) hz 0
    (Finset.mem_univ 0)
  exact hh

/-- A genuine cubic matrix cocycle has an invertible descent basis. -/
theorem linear_cocycle_descent (σ : F ≃+* F) (hs : orderOf σ = 3)
    (A : GL (Fin 3) F)
    (hA : A * GeneralLinearGroup.map σ.toRingHom A *
      GeneralLinearGroup.map σ.toRingHom (GeneralLinearGroup.map σ.toRingHom A) = 1) :
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
  have hT (v : Fin 3 → F) : T (T (T v)) = v := by
    change A.val *ᵥ (σ ∘ (A.val *ᵥ (σ ∘ (A.val *ᵥ (σ ∘ v))))) = v
    rw [hmap, hmap, hmap, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    have hm := congrArg Units.val hA
    change A.val * A.val.map σ * (A.val.map σ).map σ = 1 at hm
    rw [hm, Matrix.one_mulVec]
    ext i
    exact DFunLike.congr_fun ((orderOf_eq_prime_iff.mp hs).1) (v i)
  have hspan := cubic_fixed_span σ hs T hsemi hT
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

end Matrix.PSL3.StandardCubicFixedNine.Descent
