module

public import Theory.SpecificGroups.PSL3Four.CentralCover.GraphField

/-!
# Graph-field markings over an arbitrary four-element field

Coefficient transport commutes with inverse transpose and squaring. A field
isomorphism with the fixed four-element field therefore identifies the actual
projective graph-field actions. Composing with an automorphism conjugator
extends the marking to every member of that conjugacy class.

The group comparison uses the attributed ATLAS field transport from
`ExceptionalIsomorphisms.FieldTransportLaws`; its license and attribution are
retained there. The compatibility calculations below concern the actual
quotient maps, with no automorphism-coverage or residual-structure assumption.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.4(5), printed p.1171, and its use in 16.4.9 on p.1189.
-/

public section

namespace Matrix.PSL3Four

open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable
variable {K : Type*} [Field K]

/-- Coefficient transport intertwines inverse transpose times squaring. -/
theorem fieldEquivPSL_graphField (e : K ≃+* F) (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ 2)
    (x : PSL(3,K)) :
    Atlas.fieldEquivPSL 3 e ((graph K * Matrix.PSL3.OuterSolvable.fieldAction K σ) x) =
      (graph F * pslFrobenius) (Atlas.fieldEquivPSL 3 e x) := by
  have hmk (A : SL(3,K)) : Atlas.fieldEquivPSL 3 e (A : PSL(3,K)) =
      (Atlas.fieldEquivSL 3 e A : PSL) := Atlas.fieldEquivPSL_mk 3 e A
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(3,K)) x
  simp only [QuotientGroup.mk'_apply, MulAut.mul_apply, Matrix.PSL3.OuterSolvable.fieldAction_mk, graph_mk,
    hmk, pslFrobenius_mk]
  rw [map_inv]
  congr 2
  apply Subtype.ext
  ext i j
  change e (σ (A.val j i)) = (e (A.val j i)) ^ 2
  rw [hσ, map_pow]

/-- Every conjugate of the natural graph-field action has a compatible marking
in the fixed projective model, independently of the chosen coefficient field. -/
theorem exists_graphField_marking [Finite K] (hK : Nat.card K = 4)
    (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ 2) (a : MulAut PSL(3,K))
    (ha : IsConj a (graph K * Matrix.PSL3.OuterSolvable.fieldAction K σ)) :
    ∃ d : PSL(3,K) ≃* PSL, ∀ x,
      d (a x) = (graph F * pslFrobenius) (d x) := by
  let : Fintype K := Fintype.ofFinite K
  let : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card K = Fintype.card F := by
    simpa only [← Nat.card_eq_fintype_card, card_F] using hK
  let e := FiniteField.ringEquivOfCardEq hc
  obtain ⟨c, hc⟩ := isConj_iff.mp ha
  refine ⟨c.trans (Atlas.fieldEquivPSL 3 e), fun x => ?_⟩
  have hx := congrArg (fun b : MulAut PSL(3,K) => b (c x)) hc
  change c (a (c.symm (c x))) = (graph K * Matrix.PSL3.OuterSolvable.fieldAction K σ) (c x) at hx
  rw [c.symm_apply_apply] at hx
  change Atlas.fieldEquivPSL 3 e (c (a x)) = _
  rw [hx]
  exact fieldEquivPSL_graphField e σ hσ (c x)

end Matrix.PSL3Four
