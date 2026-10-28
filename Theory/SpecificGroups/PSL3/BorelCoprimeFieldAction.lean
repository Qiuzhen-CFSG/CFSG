module
public import Theory.SpecificGroups.PSL3.CartanActions.RootTorusFieldOrder
public import Theory.SpecificGroups.PSL3.CartanActions.ResidualInner
public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient
public import Theory.SpecificGroups.Classical.EvenDerivedThree

/-!
# Nontrivial coefficient action for coprime PSL₃ actors

Standard automorphism coverage gives a linear-field-graph factorization.
If its coefficient factor were trivial, the square would be linear and
the sixth power inner. Odd order and coprimality with the actual projective
group, whose order is divisible by three, then force the whole actor to
be trivial. The root torus detects the coefficient order exactly.

Source: Aschbacher--Smith 11.5.6(3), printed p.781; GLS3, 2.5.12 and §2.7.
-/

public section
open Subgroup Matrix Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open Matrix.PSL3.CartanActions Matrix.PSL3.CartanActions.SixCommutators
open Matrix.PSL3.CartanActions.RootTorusControl
open scoped MatrixGroups
namespace Matrix.PSL3.CartanActions.RootTorusControl
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem graph_square_linear (m : GL (Fin 3) F) :
    (linearConj F m * graph F)^2 = linearConj F (m * inverseTransposeGL F m) := by
  rw [map_mul,pow_two]
  calc
    _ = linearConj F m * (graph F * linearConj F m) * graph F := by group
    _ = linearConj F m * (linearConj F (inverseTransposeGL F m) * graph F) * graph F := by
      rw [graph_linearConj]
    _ = linearConj F m * linearConj F (inverseTransposeGL F m) := by
      have h := graph_sq F
      simpa only [pow_two,mul_assoc,mul_one] using
        congrArg (fun a => linearConj F m * linearConj F (inverseTransposeGL F m) * a) h

omit [Finite F] [CharP F 2] in
private theorem actor_trivial_coefficient_six_inner (m : GL (Fin 3) F) (ε : Bool) :
    projectiveActor F m 1 ε ^ 6 ∈ MulAut.innerSubgroup PSL(3,F) := by
  have hs : ∃ g : GL (Fin 3) F, projectiveActor F m 1 ε ^ 2 = linearConj F g := by
    cases ε
    · refine ⟨m^2,?_⟩
      simp only [projectiveActor,map_one,mul_one,Bool.false_eq_true,↓reduceIte,map_pow]
    · refine ⟨(m * reversalGL F) * inverseTransposeGL F (m * reversalGL F),?_⟩
      simp only [projectiveActor,map_one,mul_one,↓reduceIte,oppositionGraph,← mul_assoc,← map_mul]
      exact graph_square_linear F _
  obtain ⟨g,hg⟩ := hs
  rw [show (6 : ℕ) = 2*3 from rfl,pow_mul,hg]
  exact ResidualInner.linearConj_cube_inner g

/-- A nontrivial odd coprime Borel actor has nontrivial coefficient action,
even when its normal form contains a graph factor. -/
theorem exists_nontrivial_coefficient {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (α : MulAut PSL(3,F)) (hne : α ≠ 1) (ho : Odd (orderOf α))
    (hc : Nat.Coprime (orderOf α) (Nat.card PSL(3,F)))
    (hU : (unipotent F).map α.toMonoidHom = unipotent F) :
    ∃ (m : GL (Fin 3) F) (σ : F ≃+* F) (ε : Bool),
      σ ≠ 1 ∧ orderOf σ ∣ orderOf α ∧ α = projectiveActor F m σ ε := by
  have hcover := Matrix.PSL3Even.AutomorphismCoverage.standard_eq_top_of_root_orientation
    F hn hF (Matrix.PSL3Even.AutomorphismCoverage.exists_oppositionGraph_preserves_roots_of_charTwo F)
  obtain ⟨m,σ,ε,he⟩ := ActorCoverage.projectiveCoverage_of_standard_eq_top F hcover α
  refine ⟨m,σ,ε,?_,?_,he⟩
  · intro hs
    have hi : α^6 ∈ MulAut.innerSubgroup PSL(3,F) := by
      rw [he,hs]
      exact actor_trivial_coefficient_six_inner F m ε
    obtain ⟨g,hg⟩ := hi
    have he6 : α^6 = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes
        (hc.of_dvd_left (orderOf_pow_dvd (x := α) 6)) dvd_rfl (by
          rw [← hg]
          exact (orderOf_map_dvd MulAut.conj g).trans (orderOf_dvd_natCard g)))
    have hthree : 3 ∣ Nat.card PSL(3,F) :=
      (Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
        (F := F) (show (0 : Fin 3) ≠ 1 by decide)).trans (card_subgroup_dvd_card _)
    apply hne
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes (show Nat.Coprime (orderOf α) 6 from
      ho.coprime_two_right.mul_right (hc.of_dvd_right hthree)) dvd_rfl
    exact orderOf_dvd_of_pow_eq_one he6
  · exact orderOf_dvd_of_pow_eq_one (actor_coefficient_pow F hF m σ ε
      (he ▸ hU) (he ▸ pow_orderOf_eq_one α))
end Matrix.PSL3.CartanActions.RootTorusControl
