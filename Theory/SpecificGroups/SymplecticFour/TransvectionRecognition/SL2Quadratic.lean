module
public import Theory.Representation.SL2.BinaryQuadratic
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.SpecificGroups.SymplecticFour.Flag

/-!
# Quadratic refinement for the literal binary PSL₂ subgroup

An actual absolutely irreducible degree-four symplectic action of PSL₂(K),
with K finite of characteristic two, preserves a quadratic form whose polar
form is exactly the original symplectic form. The canonical SL₂-to-PSL₂
isomorphism transports the action to the proved highest-weight construction.
No quadratic form is assumed from an abstract model label.

This is the PSL₂ module branch of Aschbacher--Smith G.4.1, printed p.342;
normalizer invariance then follows from quadratic-refinement uniqueness.
-/

public section

namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
variable {F K : Type*} [Field F] [CharP F 2] [Field K] [Finite K] [CharP K 2]

theorem exists_quadratic_of_psl2_subgroup (N : Subgroup (Sp F))
    (ha : Representation.IsAbsolutelyIrreducible
      ((Representation.symplecticNatural 2).comp N.subtype))
    (e : N≃*Theory.PSL2.Group K) (f : ℕ) (hcard : Nat.card K=2^f) :
    ∃ Q : QuadraticForm F (Vector F),Q.polarBilin=form F ∧
      ∀ n : N, ∀ v,Q ((n:Sp F)•v)=Q v := by
  let ρ : Representation F N (Vector F) :=
    (Representation.symplecticNatural 2).comp N.subtype
  let : ρ.IsAbsolutelyIrreducible := ha
  exact Representation.SL2.BinaryQuadratic.exists_quadratic_of_equiv_sl2 ρ
    (by simp [Vector]) (e.trans (Theory.PSL2.sl2QuotientEquiv K).symm) f hcard
    (form F) (fun n => preserves_form (n:Sp F))
end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
