module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Periodicity of Frobenius-semilinear maps

Over an algebraic extension of a prime field, every vector is periodic under
an injective Frobenius-semilinear map of a finite-dimensional vector space.
Adjoin the finitely many matrix entries and the coordinates of the vector.
The resulting finite field gives a finite stable set on which the map is
injective, hence a permutation.

This is the finite-orbit step in elementary Frobenius descent, used for the
prime-field realization in Gorenstein, *Finite Groups*, §16.6, p.482.
-/

public section

open Module
namespace Representation.FrobeniusFixedDescent

variable {p : ℕ} [Fact p.Prime]
variable {K V ι : Type*} [Field K] [Algebra (ZMod p) K]
  [Algebra.IsAlgebraic (ZMod p) K] [AddCommGroup V] [Module K V]
  [Fintype ι] (b : Basis ι K V)
  (T : V →+ V) (hT : Function.Injective T)
  (hsemi : ∀ (a : K) (v : V), T (a • v) = a ^ p • T v)

include b hT hsemi
/-- Every vector has a positive period under an injective Frobenius-semilinear map. -/
theorem periodic (v : V) : ∃ n > 0, T^[n] v = v := by
  classical
  let s : Set K := Set.range (b.equivFun v) ∪
    Set.range (fun ij : ι × ι => b.equivFun (T (b ij.1)) ij.2)
  have hs : s.Finite := (Set.finite_range _).union (Set.finite_range _)
  let : Finite s := hs.to_subtype
  let E := IntermediateField.adjoin (ZMod p) s
  let : FiniteDimensional (ZMod p) E := IntermediateField.finiteDimensional_adjoin
    (fun x _ => Algebra.IsIntegral.isIntegral x)
  let : Finite E := Module.finite_of_finite (ZMod p)
  have hv (i : ι) : b.equivFun v i ∈ E :=
    IntermediateField.subset_adjoin (ZMod p) s (Or.inl ⟨i, rfl⟩)
  have hTb (i j : ι) : b.equivFun (T (b i)) j ∈ E :=
    IntermediateField.subset_adjoin (ZMod p) s (Or.inr ⟨(i, j), rfl⟩)
  let U := {w : V // ∀ i, b.equivFun w i ∈ E}
  let coord : U → (ι → E) := fun w i => ⟨b.equivFun w.val i, w.property i⟩
  have hc : Function.Injective coord := by
    intro w z h
    apply Subtype.ext
    apply b.equivFun.injective
    funext i
    exact congrArg Subtype.val (congrFun h i)
  let : Finite U := Finite.of_injective coord hc
  have stable (w : U) (i : ι) : b.equivFun (T w.val) i ∈ E := by
    have he : T w.val = ∑ j, (b.equivFun w.val j) ^ p • T (b j) := by
      conv_lhs => rw [← b.sum_repr w.val]
      simp only [map_sum, hsemi, Basis.equivFun_apply]
    rw [he, map_sum, Finset.sum_apply]
    apply E.sum_mem
    intro j _
    simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using
      E.mul_mem (pow_mem (w.property j) p) (hTb j i)
  let f : U → U := fun w => ⟨T w.val, stable w⟩
  have hf : Function.Injective f := by
    intro w z h
    exact Subtype.ext (hT (congrArg Subtype.val h))
  obtain ⟨n, hn, he⟩ := hf.mem_periodicPts (⟨v, hv⟩ : U)
  refine ⟨n, hn, ?_⟩
  exact he.map (show Function.Semiconj (Subtype.val : U → V) f T from fun _ => rfl)

end Representation.FrobeniusFixedDescent
