module

public import Theory.Representation.SL3.BinaryDefiningFactors
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Concrete equivalences for the exceptional binary tensor words

The restricted tensor words with exactly one natural or dual factor are
identified with the corresponding natural action.  The proof keeps the
trivial tensor factors and removes them using the equivariant tensor-unit
maps. The single-factor label and position are independent of the embedding.
Reassociation therefore identifies the doubled block with two factors of the
same label. The coefficient twist is the `2 ^ block.length` Frobenius
automorphism of the finite coefficient field. The dual case uses the pairing
`(f ⊗ g)(v ⊗ w) = f(v)g(w)` to identify the dual of the whole tensor.

Source: GLS III, 2.8.6, 2.8.8 and 2.8.10(c); Aschbacher--Smith, G.9.3(8),(17).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section

open scoped MatrixGroups TensorProduct
open Representation

namespace Representation.SL3.BinaryDefiningFactors

variable {F K : Type*} [Field F] [Field K] [CharP K 2]

/-- Tensoring an intertwining equivalence on the right. -/
noncomputable def tensorRightEquiv {G V W W' : Type*} [Group G]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup W'] [Module K W']
    {ρ : Representation K G V} {σ : Representation K G W}
    {τ : Representation K G W'} (e : σ.Equiv τ) :
    (ρ.tprod σ).Equiv (ρ.tprod τ) :=
  IntertwiningMap.ofBijective (e.toIntertwiningMap.lTensor ρ) (by
    have hmap : (e.toIntertwiningMap.lTensor ρ).toLinearMap =
        (TensorProduct.congr (LinearEquiv.refl K V) e.toLinearEquiv).toLinearMap := by
      ext x y
      rfl
    change Function.Bijective (e.toIntertwiningMap.lTensor ρ).toLinearMap
    rw [hmap]
    exact (TensorProduct.congr (LinearEquiv.refl K V) e.toLinearEquiv).bijective)

/-- Tensoring two actual representation equivalences. -/
def tensorEquiv {G V V' W W' : Type*} [Group G]
    [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module K W']
    {ρ : Representation K G V} {ρ' : Representation K G V'}
    {τ : Representation K G W} {τ' : Representation K G W'}
    (e : ρ.Equiv ρ') (f : τ.Equiv τ') : (ρ.tprod τ).Equiv (ρ'.tprod τ') where
  toLinearEquiv := _root_.TensorProduct.congr e.toLinearEquiv f.toLinearEquiv
  isIntertwining' := (e.toIntertwiningMap.tensor f.toIntertwiningMap).isIntertwining'

/-- The actual dual-of-a-tensor equivalence. -/
noncomputable def dualTensorEquiv {G V W : Type*} [Group G]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (ρ : Representation K G V) (σ : Representation K G W) :
    (ρ.dual.tprod σ.dual).Equiv (ρ.tprod σ).dual := by
  refine Representation.Equiv.mk (TensorProduct.dualDistribEquiv K V W) ?_
  intro g
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro x
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z₁ z₂ ih₁ ih₂ =>
    simp only [map_add, LinearMap.add_apply, ih₁, ih₂]
  | tmul f h =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x₁ x₂ ih₁ ih₂ =>
      simp only [map_add, ih₁, ih₂]
    | tmul v w =>
      simp [Representation.tprod_apply, Representation.dual_apply,
        TensorProduct.dualDistribEquiv, TensorProduct.dualDistribEquivOfBasis,
        TensorProduct.dualDistrib_apply, Module.Dual.transpose_apply]

private theorem wordRep_trivial_equiv (ι : F →+* K)
    (w : List Factor) (ha : naturalCount w = 0) (hb : adjointCount w = 0) :
    Nonempty ((wordRep ι w).Equiv (Representation.trivial K SL(3,F) K)) := by
  induction w generalizing ι with
  | nil => exact ⟨Representation.Equiv.refl _⟩
  | cons a w ih =>
    cases a with
    | trivial =>
      have ha' : naturalCount w = 0 := by simpa [naturalCount] using ha
      have hb' : adjointCount w = 0 := by simpa [adjointCount] using hb
      obtain ⟨e⟩ := ih ((frobenius K 2).comp ι) ha' hb'
      exact ⟨(Representation.TensorProduct.lid K _).trans e⟩
    | natural => simp [naturalCount] at ha
    | dual => simp [naturalCount] at ha
    | adjoint => simp [adjointCount] at hb

/-- Splitting a word at an append boundary, with the accumulated Frobenius twist. -/
theorem wordRep_append_equiv (ι : F →+* K) (u v : List Factor) :
    Nonempty ((wordRep ι (u ++ v)).Equiv
      ((wordRep ι u).tprod
        (wordRep ((iterateFrobenius K 2 u.length).comp ι) v))) := by
  induction u generalizing ι with
  | nil =>
      simpa [wordRep, iterateFrobenius_zero] using
        (⟨(Representation.TensorProduct.lid K (wordRep ι v)).symm⟩ :
          Nonempty ((wordRep ι v).Equiv
            ((Representation.trivial K SL(3,F) K).tprod (wordRep ι v))))
  | cons a u ih =>
      obtain ⟨e⟩ := ih ((frobenius K 2).comp ι)
      let e' := tensorRightEquiv e (ρ := factorRep ι a)
      refine ⟨e'.trans ?_⟩
      simpa [wordRep, List.length, iterateFrobenius_add, Function.comp_def,
        RingHom.comp_assoc] using
        (Representation.TensorProduct.assoc (factorRep ι a)
          (wordRep ((frobenius K 2).comp ι) u)
          (wordRep ((iterateFrobenius K 2 u.length).comp ((frobenius K 2).comp ι)) v)).symm


/-- The nontrivial label and its position can be chosen independently of the
coefficient embedding. Thus a repeated block retains the same duality label. -/
theorem wordRep_single_factor_uniform (b : List Factor)
    (ha : naturalCount b = 1) (hb : adjointCount b = 0) :
    ∃ (j : ℕ) (a : Factor), j < b.length ∧ (a = .natural ∨ a = .dual) ∧
      ∀ ι : F →+* K, Nonempty ((wordRep ι b).Equiv
        (factorRep ((iterateFrobenius K 2 j).comp ι) a)) := by
  induction b with
  | nil => simp [naturalCount] at ha
  | cons a b ih =>
    cases a with
    | trivial =>
      have ha' : naturalCount b = 1 := by simpa [naturalCount] using ha
      have hb' : adjointCount b = 0 := by simpa [adjointCount] using hb
      obtain ⟨j, a, hj, ha, he⟩ := ih ha' hb'
      refine ⟨j + 1, a, by simpa using Nat.succ_lt_succ hj, ha, ?_⟩
      intro ι
      obtain ⟨e⟩ := he ((frobenius K 2).comp ι)
      refine ⟨?_⟩
      change ((Representation.trivial K SL(3,F) K).tprod
        (wordRep ((frobenius K 2).comp ι) b)).Equiv
          (factorRep ((iterateFrobenius K 2 (j + 1)).comp ι) a)
      rw [iterateFrobenius_add, iterateFrobenius_one, RingHom.comp_assoc]
      exact (Representation.TensorProduct.lid K _).trans e
    | natural =>
      have ha' : naturalCount b = 0 := by simpa [naturalCount] using ha
      have hb' : adjointCount b = 0 := by simpa [adjointCount] using hb
      refine ⟨0, .natural, by simp, Or.inl rfl, ?_⟩
      intro ι
      obtain ⟨e⟩ := wordRep_trivial_equiv ((frobenius K 2).comp ι) b ha' hb'
      refine ⟨?_⟩
      simpa [wordRep, factorRep] using
        (tensorRightEquiv e).trans (Representation.TensorProduct.rid K (natural ι))
    | dual =>
      have ha' : naturalCount b = 0 := by simpa [naturalCount] using ha
      have hb' : adjointCount b = 0 := by simpa [adjointCount] using hb
      refine ⟨0, .dual, by simp, Or.inr rfl, ?_⟩
      intro ι
      obtain ⟨e⟩ := wordRep_trivial_equiv ((frobenius K 2).comp ι) b ha' hb'
      refine ⟨?_⟩
      simpa [wordRep, factorRep] using
        (tensorRightEquiv e).trans (Representation.TensorProduct.rid K (natural ι).dual)
    | adjoint => simp [adjointCount] at hb

/-- A word with one nontrivial factor is an actual natural or dual action. -/
theorem wordRep_single_factor (ι : F →+* K) (b : List Factor)
    (ha : naturalCount b = 1) (hb : adjointCount b = 0) :
    ∃ ι' : F →+* K,
      Nonempty ((wordRep ι b).Equiv (natural ι')) ∨
      Nonempty ((wordRep ι b).Equiv (natural ι').dual) := by
  obtain ⟨j, a, _, ha, he⟩ := wordRep_single_factor_uniform (F := F) (K := K) b ha hb
  refine ⟨(iterateFrobenius K 2 j).comp ι, ?_⟩
  rcases ha with rfl | rfl
  · exact Or.inl (he ι)
  · exact Or.inr (he ι)

variable [Finite F] [CharP F 2]

/-- Frobenius on the coefficient field agrees with Frobenius on the image
of every embedding into the representation field. -/
theorem comp_iterateFrobeniusEquiv (ι : F →+* K) (r : ℕ) :
    ι.comp (iterateFrobeniusEquiv F 2 r).toRingHom =
      (iterateFrobenius K 2 r).comp ι := by
  ext a
  exact map_pow ι a (2 ^ r)

/-- Doubling a single-factor block gives the two natural Frobenius conjugates,
or the actual dual of their whole tensor product. No period or classification
hypothesis is needed. -/
theorem wordRep_double_single_factor (ι : F →+* K) (b : List Factor)
    (ha : naturalCount b = 1) (hb : adjointCount b = 0) :
    ∃ σ : F ≃+* F, (∀ a, σ a = a ^ (2 ^ b.length)) ∧
      ∃ ι' : F →+* K,
        Nonempty ((wordRep ι (List.replicate 2 b).flatten).Equiv
          ((natural ι').tprod (natural (ι'.comp σ.toRingHom)))) ∨
        Nonempty ((wordRep ι (List.replicate 2 b).flatten).Equiv
          ((natural ι').tprod (natural (ι'.comp σ.toRingHom))).dual) := by
  have hw : (List.replicate 2 b).flatten = b ++ b := by simp [List.replicate_succ]
  rw [hw]
  obtain ⟨j, a, _, ha, he⟩ := wordRep_single_factor_uniform (F := F) (K := K) b ha hb
  let σ := iterateFrobeniusEquiv F 2 b.length
  let ι' := (iterateFrobenius K 2 j).comp ι
  refine ⟨σ, fun _ => rfl, ι', ?_⟩
  have hc : (iterateFrobenius K 2 j).comp
      ((iterateFrobenius K 2 b.length).comp ι) = ι'.comp σ.toRingHom := by
    rw [← comp_iterateFrobeniusEquiv ι b.length, ← RingHom.comp_assoc]
  obtain ⟨e₀⟩ := wordRep_append_equiv ι b b
  obtain ⟨e₁⟩ := he ι
  obtain ⟨e₂⟩ := he ((iterateFrobenius K 2 b.length).comp ι)
  rw [hc] at e₂
  have e := e₀.trans (tensorEquiv e₁ e₂)
  rcases ha with rfl | rfl
  · left
    exact ⟨e⟩
  · right
    have e' := e.trans (dualTensorEquiv (natural ι') (natural (ι'.comp σ.toRingHom)))
    exact ⟨e'⟩

end Representation.SL3.BinaryDefiningFactors
