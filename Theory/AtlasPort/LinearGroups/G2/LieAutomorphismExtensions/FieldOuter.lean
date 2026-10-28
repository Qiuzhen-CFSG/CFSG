module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.FieldAction
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.CharP.Two

/-!
# Field automorphisms of G₂ are outer

The trace of the actual eight-dimensional octonion representation on
`rootF t * weylS` is `-t²`. Conjugation preserves that trace, whereas
coefficientwise field transport applies the field automorphism to it.
Injectivity of squaring in characteristic two therefore detects the field
component, including over the binary field. No description of all abstract
automorphisms is assumed.

Source: the field-component argument used in Aschbacher--Smith F.1.12,
printed p.264; the root and Weyl formulas are the licensed ATLAS port.
-/

namespace Atlas.G2.LieAutomorphismExtensions
open Atlas.SplitOctonion Explicit
variable {F : Type*} [Field F]

private noncomputable def actionTrace (g : Model F) : F :=
  LinearMap.trace F (Carrier F) g.val.toLinearMap

private theorem actionTrace_eq_sum (g : Model F) :
    actionTrace g = ∑ i : Fin 8, g.val (basisVector i) i := by
  rw [actionTrace, LinearMap.trace_eq_matrix_trace F (Pi.basisFun F (Fin 8))]
  rfl

private theorem actionTrace_conj (g x : Model F) :
    actionTrace (g * x * g⁻¹) = actionTrace x := by
  exact LinearMap.trace_conj' x.val.toLinearMap g.val

private theorem actionTrace_field (σ : F ≃+* F) (g : Model F) :
    actionTrace (fieldAction σ g) = σ (actionTrace g) := by
  rw [actionTrace_eq_sum, actionTrace_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hb : mapCoefficients σ (basisVector i) = basisVector i := by
    funext j
    simp [mapCoefficients, basisVector, Pi.single_apply, apply_ite σ]
  change (fieldEquiv σ g).val (basisVector i) i = _
  conv_lhs => rw [← hb, fieldEquiv_action]
  rfl

private theorem actionTrace_rootF_weylS (t : F) :
    actionTrace (rootF t * weylS) = -(t ^ 2) := by
  rw [actionTrace_eq_sum]
  have hd (i : Fin 8) : (rootF t * weylS).val (basisVector i) i =
      (![t,0,-(t^2),0,0,0,-t,0] : Fin 8 → F) i := by
    fin_cases i <;> simp [rootF, rootFEquiv, rootFLinear, rootFApply,
      weylS, weylSEquiv, weylSLinear, weylSApply, basisVector]
  simp_rw [hd]
  simp [Fin.sum_univ_succ]

/-- An inner coefficientwise field automorphism has trivial field component. -/
public theorem fieldAction_eq_conj_implies_one [CharP F 2] (σ : F ≃+* F) (g : Model F)
    (h : fieldAction σ = MulAut.conj g) : σ = 1 := by
  apply RingEquiv.ext
  intro t
  change σ t = t
  have ht := congrArg actionTrace (MulEquiv.congr_fun h (rootF t * weylS))
  rw [actionTrace_field, MulAut.conj_apply, actionTrace_conj,
    actionTrace_rootF_weylS, map_neg, map_pow, neg_inj] at ht
  simpa only [CharTwo.neg_eq, or_self] using (sq_eq_sq_iff_eq_or_eq_neg.mp ht)
end Atlas.G2.LieAutomorphismExtensions
