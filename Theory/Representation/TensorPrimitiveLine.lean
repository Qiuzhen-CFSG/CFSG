module
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Highest lines in a tensor product

A basis expansion shows that the common right-factor primitive space consists
of tensors with the right highest vector. The left operators then recover
the left highest line. The accompanying spanning implication tensors two
cyclic word spans. These are the linear algebra steps required for the actual
Ree finite-restriction tensor, Steinberg (1963), proofs 5.1(1) and 12.2.
-/

public section

open scoped TensorProduct BigOperators
namespace TensorProduct.PrimitiveLine
variable {F V W I J : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [FiniteDimensional F V]

private lemma right_primitive (Q : J → Module.End F W) (w : W)
    (hQ : ∀ y, (∀ j, Q j y = 0) ↔ y ∈ Submodule.span F {w})
    (z : V ⊗[F] W) (hz : ∀ j, TensorProduct.map LinearMap.id (Q j) z = 0) :
    ∃ x : V, z = x ⊗ₜ[F] w := by
  classical
  let b := Module.finBasis F V
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := W) b
  have hc (i : Fin (Module.finrank F V)) : e z i ∈ Submodule.span F {w} := by
    apply (hQ _).mp
    intro j
    have he (z : V ⊗[F] W) : e (TensorProduct.map LinearMap.id (Q j) z) i = Q j (e z i) := by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [e]
      | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
    rw [← he, hz, map_zero, Finsupp.zero_apply]
  choose c hc using fun i => Submodule.mem_span_singleton.mp (hc i)
  refine ⟨∑ i, c i • b i, ?_⟩
  apply e.injective
  ext i
  simpa [e, Finsupp.single_apply] using (hc i).symm

theorem primitive_iff (P : I → Module.End F V) (Q : J → Module.End F W)
    (v : V) (w : W) (hw : w ≠ 0)
    (hP : ∀ x, (∀ i, P i x = 0) ↔ x ∈ Submodule.span F {v})
    (hQ : ∀ y, (∀ j, Q j y = 0) ↔ y ∈ Submodule.span F {w})
    (z : V ⊗[F] W) :
    ((∀ i, TensorProduct.map (P i) LinearMap.id z = 0) ∧
      (∀ j, TensorProduct.map LinearMap.id (Q j) z = 0)) ↔
      z ∈ Submodule.span F {v ⊗ₜ[F] w} := by
  constructor
  · rintro ⟨hleft, hright⟩
    obtain ⟨x, rfl⟩ := right_primitive Q w hQ z hright
    have hx : x ∈ Submodule.span F {v} := by
      apply (hP x).mp
      intro i
      obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one F hw
      have h := congrArg (fun z : V ⊗[F] W =>
        TensorProduct.rid F V (TensorProduct.map LinearMap.id ℓ z)) (hleft i)
      simpa [TensorProduct.map_tmul, hℓ] using h
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    exact Submodule.mem_span_singleton.mpr ⟨c, (TensorProduct.smul_tmul' c v w).symm⟩
  · intro hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have hp := (hP v).mpr (Submodule.subset_span (Set.mem_singleton v))
    have hq := (hQ w).mpr (Submodule.subset_span (Set.mem_singleton w))
    constructor <;> intro i
    · simp [map_smul, TensorProduct.map_tmul, hp]
    · simp [map_smul, TensorProduct.map_tmul, hq]

end TensorProduct.PrimitiveLine
