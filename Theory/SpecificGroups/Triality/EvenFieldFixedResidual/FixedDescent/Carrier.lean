module

public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.Twist
public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedDescent
public import Theory.GroupAction.AutomorphismFixedResidualTransport
/-!
# Coefficient fixed points through the elementary central quotient

In characteristic two the proved fixed Bruhat normal form makes the elementary
subgroup the full graph-field fixed group. The proved triviality of its own
center makes the quotient map bijective. Their composite intertwines the exact
coefficient actions, so it restricts to an equivalence of fixed subgroups.
Combined with the square/cube identities, this identifies the carrier fixed
points with the inverse-diagram half-parameter fixed group. No simplicity or
perfectness premise, and no exclusion of the smallest field, is needed.

This supplies the elementary and central-quotient steps of the field descent
in Aschbacher–Smith 16.1.4(4), printed p.1171 (`refs/quasithin.pdf`), following
GLS3 §§2.2 and 2.5 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
open Triality.Standard Triality.Standard.OuterOdd
open Triality.Standard.ConcreteBruhat.FixedDescent
noncomputable section
namespace Triality.Standard.EvenField

private theorem through_surjective {E G H : Type*} (π : E → G)
    (hπ : Function.Surjective π) (f g : G → H)
    (h : ∀ x, f (π x) = g (π x)) (y : G) : f y = g y := by
  obtain ⟨x, rfl⟩ := hπ y
  exact h x

/-- The original carrier-to-fixed-group equivalence intertwines coefficient actions. -/
theorem carrierFixedEquiv_coefficient (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) (x : Carrier P) :
    carrierFixedEquiv P hp (coefficientAction P e x) =
      coefficientFixed P e (carrierFixedEquiv P hp x) :=
  through_surjective (toCarrier P) (toCarrier_surjective P)
    (fun z => carrierFixedEquiv P hp (coefficientAction P e z))
    (fun z => coefficientFixed P e (carrierFixedEquiv P hp z))
    (fun g => (congrArg (carrierFixedEquiv P hp) (coefficientCarrier_toCarrier P e g)).trans
      ((carrierFixedEquiv_toCarrier P hp (coefficientElementary P e g)).trans
        ((coefficientElementary_val P e g).trans
          (congrArg (coefficientFixed P e) (carrierFixedEquiv_toCarrier P hp g).symm)))) x

/-- Fixed points commute with the actual elementary and central-quotient equivalence. -/
def carrierCoefficientFixedEquiv (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) :
    (coefficientAction P e).fixedSubgroup ≃* MulAut.fixedSubgroup (coefficientFixed P e) :=
  MulAut.fixedSubgroupEquivOfCompatible (carrierFixedEquiv P hp) _ _
    (carrierFixedEquiv_coefficient P hp e)

/-- The coefficient fixed group of the original carrier, before subfield descent. -/
def carrierCoefficientFixedEquivInverseGraph (n : ℕ) (hn : 0 < n)
    (m : ℕ) (hnm : n = 2*m) :
    (coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m))).fixedSubgroup ≃*
      (inverseGraphHalf n hn m).fixedSubgroup :=
  (carrierCoefficientFixedEquiv (binaryParameters n hn) rfl _).trans
    (coefficientFixedEquivInverseGraph n hn m hnm)

end Triality.Standard.EvenField
