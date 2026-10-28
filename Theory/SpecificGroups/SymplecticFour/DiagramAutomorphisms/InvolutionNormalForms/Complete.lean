module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.FieldDescent
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.GraphDescent
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification

/-!
# Actual involution normal forms in even symplectic groups

Semilinear coverage and the field and graph cocycle descents discharge all
premises of the outer-quotient reduction. Thus an involution of Aut(Sp₄(F))
is inner or genuinely conjugate to the appropriate field or graph involution.
The graph descent retains an actual symplectic conjugator over F.

Source: Aschbacher–Smith, Quasithin, Lemma 16.1.4 (printed pp.1170–1173),
as used in 2.5.19 and E.6.23. The binary derived carrier is separate.
-/

public section
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
open ExceptionalGraph
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Every involution has one of the actual inner, field, or graph conjugacy forms. -/
theorem involution_normalForms {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)
    (a : MulAut (Sp F)) (ha : orderOf a = 2) :
    (∃ g : Sp F, orderOf g = 2 ∧ a = MulAut.conj g) ∨
      (Even n ∧ IsConj a (fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)))) ∨
      (Odd n ∧ IsConj a (graphAut ^ n)) := by
  exact involution_normalForms_of_coboundaries hcard hn
    SemilinearClassification.inner_field_of_preservesDiagram
    (half_frobenius_cocycle_coboundary hcard hn)
    (fun _ => graph_cocycle_coboundary hcard (by omega)) a ha

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
