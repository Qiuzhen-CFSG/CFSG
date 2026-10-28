module

public import Theory.SpecificGroups.PSL3.CartanActions.SixCommutators.TwistedActors
public import Theory.SpecificGroups.PSL3.CartanActions.SixCommutators.LinearFactor

/-!
# Every outer two-element preserving the standard degree-six Sylow

Use a raw matrix automorphism factorization, with the entire GL₃ factor
retained. Sylow preservation forces that factor to be upper triangular;
its action on the Borel quotient is already computed. A nontrivial field
part or any graph part gives the explicit displacement lower bound.
If both parts vanish, the two-element is inner by the odd-power determinant
argument, contrary to outerness. The original actor is never replaced by
an involution power.

The sole classification input is universal coverage by the literal linear,
field and graph automorphisms. No quotient-action or cardinality conclusion
is part of that input. Source: GLS3 Theorem 2.5.12 and §2.7;
Aschbacher–Smith, proof of 13.8.20, printed p.954.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open Matrix.PSL3.CartanActions.BorelQuotient
namespace Matrix.PSL3.CartanActions.SixCommutators
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

theorem special_standard_outer_bound (hF : Nat.card F = 2 ^ 6)
    (hcover : SpecialCoverage F) (α : MulAut SL(3,F))
    (hU : (unipotentSL F).map α.toMonoidHom = unipotentSL F)
    (hα : ∃ k : ℕ, α ^ (2 ^ k) = 1) (ho : α ∉ MulAut.innerSubgroup SL(3,F)) :
    let C := commutatorSubgroup (zpowers α) SL(3,F) (borelSL F)
    3 < Nat.card (C ⧸ pCore 2 C) := by
  obtain ⟨m,σ,ε,rfl⟩ := hcover α
  have hB : (borelSL F).map (specialActor F m σ ε).toMonoidHom = borelSL F := by
    rw [← normalizer_unipotentSL, map_equiv_normalizer_eq, hU]
  have hp := centerAction_unipotent F (specialActor F m σ ε) hU
  rw [centerAction_specialActor] at hp
  have hm := linear_part_unipotent F m σ ε hp
  cases ε with
  | false =>
    by_cases hσ : σ = 1
    · subst σ
      have hf : Atlas.fieldEquivSL 3 (1 : F ≃+* F) = 1 := by
        apply MulEquiv.ext
        intro x
        apply Subtype.ext
        rfl
      have he : specialActor F m 1 false = linearConjSL F m := by
        simp only [specialActor, Bool.false_eq_true, ↓reduceIte, hf, mul_one]
      rw [he] at hα ho
      exact (ho (special_linear_two_element_inner F hF m hα)).elim
    · exact special_twisted_field_bound F hF m σ hσ hm hB
  | true => exact special_twisted_graph_bound F hF m σ hm hB

theorem projective_standard_outer_bound (hF : Nat.card F = 2 ^ 6)
    (hcover : ProjectiveCoverage F) (α : MulAut PSL(3,F))
    (hU : (unipotent F).map α.toMonoidHom = unipotent F)
    (hα : ∃ k : ℕ, α ^ (2 ^ k) = 1) (ho : α ∉ MulAut.innerSubgroup PSL(3,F)) :
    let C := commutatorSubgroup (zpowers α) PSL(3,F) (borel F)
    3 < Nat.card (C ⧸ pCore 2 C) := by
  obtain ⟨m,σ,ε,rfl⟩ := hcover α
  have hB : (borel F).map (projectiveActor F m σ ε).toMonoidHom = borel F := by
    rw [← normalizer_unipotent F (by decide : 0 < 6) hF, map_equiv_normalizer_eq, hU]
  have hm := linear_part_unipotent F m σ ε hU
  cases ε with
  | false =>
    by_cases hσ : σ = 1
    · subst σ
      have he : projectiveActor F m 1 false = linearConj F m := by
        simp only [projectiveActor, Bool.false_eq_true, ↓reduceIte, map_one, mul_one]
      rw [he] at hα ho
      exact (ho (projective_linear_two_element_inner F hF m hα)).elim
    · exact projective_twisted_field_bound F hF m σ hσ hm hB
  | true => exact projective_twisted_graph_bound F hF m σ hm hB

end Matrix.PSL3.CartanActions.SixCommutators
