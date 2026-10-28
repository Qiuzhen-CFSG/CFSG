module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Inputs
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Balance.Actions
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Balance.WeightCensus

/-!
# Assembly of binary Ree short/long balance from the actual torus weights

The binary Ree equation gives equality of the displacement ranks on
the short ideal and its quotient, after arbitrary conjugacy in the actual
algebraic carrier. The two torus rank formulas identify these ranks with the
moving characters in the short and long tables. Their root-table bijections
account for every actual root weight and the two fixed Cartan coordinates in
each action. Subtracting the equal ranks proves equality of fixed-weight counts.

The theorem `balance` discharges both rank premises and proves `Balance` for
every algebraically closed characteristic-two field. Placement is independent;
the literal conjugacy in the definition of `Balance` remains an explicit input.

Source: Guralnick--Malle II, Lemma 8.8 (internal p.57); GLS3, Sections 1.14 and
2.8. The consumer is `coverage_of_placement_balance_spectrum`.
-/

public section
open scoped Classical
open ReeF4.BinaryDegree.ExceptionalTensor
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Balance
variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]

/-- The two concrete torus rank formulae complete the binary Ree balance.
Their separate proof must identify the actual ideal and quotient weights. -/
theorem balance_of_torus_rank_counts
    (hshort : ∀ t : Fin 4 → Fˣ,
      (shortAction (corootTorusElement t) - 1).rank +
        fixedWeightCount EndNode.endOrbitWeight t = 24)
    (hlong : ∀ t : Fin 4 → Fˣ,
      (quotientAction (corootTorusElement t) - 1).rank +
        fixedWeightCount longOrbitWeight t = 24) :
    TorusCoverage.Balance F := by
  intro f x _ c t he
  have hr := torus_displacement_ranks_eq f x c t he
  have hs := hshort t
  have hl := hlong t
  change fixedWeightCount EndNode.endOrbitWeight t = fixedWeightCount longOrbitWeight t
  omega

/-- The binary Ree fixed equation forces short/long character balance in every
literal positive-coroot torus presentation. This supplies the balance premise
of `coverage_of_placement_balance_spectrum`. -/
theorem balance : TorusCoverage.Balance F :=
  balance_of_torus_rank_counts short_torus_rank_count quotient_torus_rank_count

end ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Balance
