module
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.SixSylowFixer

/-!
# A product-class four-group in the marked Higman–Sims centralizer

The certified complement row 66 and its product with the marked involution
have no fixed letters in the degree-100 action. Both have order two. The
complete two-class theorem therefore places both in the product class.
Together with their literal commutation relation, this supplies the three
order-four lifts needed to correct a central conjugacy defect in a double
cover of HS.

Source: Aschbacher–Smith 2.5.19, printed p.562; the inner HS classes are
16.1.5(10), printed p.1172, and the covering orders are I.2.2(5b).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.FullA6.HSProductTwist
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims
open Sporadic.LeechRelated.HS
open HSInner.ClassCoverage HSInner.ClassCoverage.ProductEmbedding
set_option maxRecDepth 20000

/-- The exact complement word giving the second product-class involution. -/
def r : Carrier := ComplementCertificate.element 66

private theorem r_mem_H : r ∈ H := ComplementCertificate.element_mem 66

/-- The two specified involutions commute in the actual HS carrier. -/
theorem commute : Commute t r := by
  exact (mem_centralizer_singleton_iff.mp (H_le_centralizer r_mem_H)).symm

private theorem r_square : r ^ 2 = 1 := by
  apply Sporadic.LeechRelated.HS.inclusion_injective
  apply Equiv.ext
  have h : ∀ p : Fin 100, inclusion (r ^ 2) p = p := by
    apply Certificate.allFin
    decide +kernel
  exact h

private theorem r_fixedPointFree : ∀ p : Fin 100, inclusion r p ≠ p := by
  apply Certificate.allFin
  decide +kernel

private theorem product_fixedPointFree : ∀ p : Fin 100, inclusion (t * r) p ≠ p := by
  apply Certificate.allFin
  decide +kernel

theorem r_order : orderOf r = 2 := by
  apply orderOf_eq_prime r_square
  intro he
  exact r_fixedPointFree 0 (by rw [he, map_one]; rfl)

theorem product_order : orderOf (t * r) = 2 := by
  apply orderOf_eq_prime
  · rw [commute.mul_pow, (orderOf_eq_prime_iff.mp t_order).1, r_square, one_mul]
  · intro he
    exact product_fixedPointFree 0 (by rw [he, map_one]; rfl)

private theorem product_class_of_fixedPointFree (x : Carrier) (hx : orderOf x = 2)
    (hfree : ∀ p : Fin 100, inclusion x p ≠ p) : IsConj t x := by
  rcases involution_classes x hx with h | h
  · obtain ⟨g, hg⟩ := isConj_iff.mp h
    have he : x * g = g * EvenLocalCandidates.e0 := by rw [← hg]; group
    have h0 : inclusion EvenLocalCandidates.e0 0 = 0 := by decide +kernel
    have hp := congrArg (fun y : Carrier => inclusion y 0) he
    exfalso
    apply hfree (inclusion g 0)
    simpa only [map_mul, Equiv.Perm.mul_apply, h0] using hp
  · exact h

/-- The second involution has the same literal carrier class as t. -/
theorem r_isConj : IsConj t r :=
  product_class_of_fixedPointFree r r_order r_fixedPointFree

/-- Their product also has the same literal carrier class as t. -/
theorem product_isConj : IsConj t (t * r) :=
  product_class_of_fixedPointFree (t * r) product_order product_fixedPointFree

/-- Three nonidentity product-class elements in one actual four-group.
The cover argument consumes both conjugacies to identify all three squares. -/
theorem exists_commuting_product_class_pair :
    ∃ r : Carrier, Commute t r ∧ orderOf r = 2 ∧ orderOf (t * r) = 2 ∧
      IsConj t r ∧ IsConj t (t * r) :=
  ⟨r, commute, r_order, product_order, r_isConj, product_isConj⟩

end CFSG.Quasithin.Chapter2.Section05.Overcomponents.FullA6.HSProductTwist
