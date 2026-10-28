module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Dual
public import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# Nondegenerate odd-dimensional quadratic spaces

This module constructs the split quadratic space of dimension `2 * m + 1`
needed for the standard type-B algebraic-group model.  On
`(Dual k W x W) x k`, with `W = Fin m -> k`, the form is
`((f, w), z) |-> f w + z ^ 2`.

The hyperbolic summand forces both `f` and `w` to vanish in the kernel of the
polar form.  In characteristic two, the remaining line is the polar radical,
but the square term is zero only at zero.  Thus the quadratic radical is zero
and the polar radical has rank at most one, exactly Mathlib's current
`QuadraticMap.Nondegenerate` criterion.  This is the standard split odd
quadratic space; the radical convention follows
Elman--Karpenko--Merkurjev, Chapter II, section 7, as cited by Mathlib.
-/

universe u

open scoped Module

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

private abbrev OddQuadraticSpace (k : Type u) [Field k] (m : Nat) :=
  Prod (Prod (Module.Dual k (Fin m -> k)) (Fin m -> k)) k

private noncomputable def oddQuadraticForm (k : Type u) [Field k] (m : Nat) :
    QuadraticForm k (OddQuadraticSpace k m) :=
  (QuadraticForm.dualProd k (Fin m -> k)).prod (QuadraticMap.sq (R := k))

private lemma oddQuadraticForm_apply (m : Nat) (x : OddQuadraticSpace k m) :
    oddQuadraticForm k m x = x.1.1 x.1.2 + x.2 * x.2 := by
  rfl

private lemma oddQuadraticForm_polar (m : Nat)
    (x y : OddQuadraticSpace k m) :
    QuadraticMap.polar (oddQuadraticForm k m) x y =
      x.1.1 y.1.2 + y.1.1 x.1.2 + (x.2 * y.2 + y.2 * x.2) := by
  simp [QuadraticMap.polar, oddQuadraticForm_apply]
  ring

private lemma hyperbolic_eq_zero_of_polar_eq_zero (m : Nat)
    (x : OddQuadraticSpace k m)
    (hx : (oddQuadraticForm k m).polarBilin x = 0) :
    x.1.1 = 0 /\ x.1.2 = 0 := by
  constructor
  · apply LinearMap.ext
    intro w
    have h := congr_arg (fun L => L (((0, w), 0) : OddQuadraticSpace k m)) hx
    simpa [QuadraticMap.polarBilin_apply_apply, oddQuadraticForm_polar] using h
  · apply Module.eval_apply_injective k
    apply LinearMap.ext
    intro g
    have h := congr_arg (fun L => L (((g, 0), 0) : OddQuadraticSpace k m)) hx
    simpa [Module.Dual.eval, QuadraticMap.polarBilin_apply_apply,
      oddQuadraticForm_polar] using h

private theorem oddQuadraticForm_nondegenerate (m : Nat) :
    (oddQuadraticForm k m).Nondegenerate := by
  constructor
  · apply le_antisymm
    · intro x hx
      change oddQuadraticForm k m x = 0 /\
        (oddQuadraticForm k m).polarBilin x = 0 at hx
      obtain ⟨hf, hw⟩ := hyperbolic_eq_zero_of_polar_eq_zero m x hx.2
      have hz : x.2 = 0 := by
        apply mul_self_eq_zero.mp
        simpa [oddQuadraticForm_apply, hf, hw] using hx.1
      apply Prod.ext
      · exact Prod.ext hf hw
      · exact hz
    · exact bot_le
  · let K := (oddQuadraticForm k m).polarBilin.ker
    let e : OddQuadraticSpace k m := ((0, 0), 1)
    have hK : K ≤ k ∙ e := by
      intro x hx
      have hpolar : (oddQuadraticForm k m).polarBilin x = 0 :=
        LinearMap.mem_ker.mp hx
      obtain ⟨hf, hw⟩ := hyperbolic_eq_zero_of_polar_eq_zero m x hpolar
      have hxe : x = x.2 • e := by
        apply Prod.ext
        · apply Prod.ext
          · simp [e, hf]
          · simp [e, hw]
        · simp [e]
      rw [hxe]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton e))
    exact (Submodule.rank_mono hK).trans ((rank_span_le {e}).trans_eq (by simp))

/-- An algebraically closed field has a nondegenerate quadratic space of every
odd dimension `2 * m + 1` with `2 ≤ m`, including in characteristic two. -/
public theorem exists_nondegenerate_odd_quadratic_space [IsAlgClosed k]
    (m : Nat) (_hm : 2 ≤ m) :
    ∃ V : Type u, ∃ _ : AddCommGroup V, ∃ _ : Module k V,
      ∃ _ : FiniteDimensional k V, ∃ q : QuadraticForm k V,
        Module.finrank k V = 2 * m + 1 ∧ q.Nondegenerate := by
  refine ⟨OddQuadraticSpace k m, inferInstance, inferInstance, inferInstance,
    oddQuadraticForm k m, ?_, oddQuadraticForm_nondegenerate m⟩
  simp [OddQuadraticSpace, Module.finrank_prod, Subspace.dual_finrank_eq]
  omega

end Theory.AlgebraicGroup
