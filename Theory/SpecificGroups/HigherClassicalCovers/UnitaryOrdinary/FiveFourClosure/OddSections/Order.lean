module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.Order.Lines
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourScalarKernel
public import Theory.SpecificGroups.ClassicalUnitary.FiveFourParabolicCardinality
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.Three
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections.Cyclic

/-!
# The concrete order of SU₅(4) and its odd-primary applications

The actual line stabilizer has five times the projective parabolic order.
Its index is 17425, obtained by structural isotropic-vector counting and
special-unitary transitivity. Multiplication gives the exact order
`2^20 * 3^2 * 5^5 * 13 * 17 * 41` of the stored matrix group. In particular,
no ambient-order, simplicity, universality or covering-kernel bound is assumed.

The last two results discharge the order premise in the existing three-
and seventeen-primary covering calculations, with their literal maps intact.
The five-primary calculation and the final multiplier assembly are separate.

Source: the classical geometry and covers in GLS3, Sections 2.7 and 6.1;
Aschbacher--Smith I.1.4(4), printed p.408 of `refs/quasithin.pdf`.
-/

public section

open BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.UnitaryFive
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections
variable {F : Type*} [Field F] [Finite F]

/-- The exact order of the literal special-unitary matrix group SU₅(4). -/
theorem card_specialSubgroup_four (J : HermitianForm 5 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4)
    (hJ : J.form = 1) :
    Nat.card J.specialSubgroup = 2^20 * 3^2 * 5^5 * 13 * 17 * 41 := by
  let : CharP F 2 := charP_two_of_card_sixteen hcard
  have hi : (specialStabilizer J (line F)).index = 17425 :=
    (Order.index_line_stabilizer J hcard hconj hJ).trans
      (Order.card_isotropic_lines J hcard hconj)
  have hs := card_specialStabilizer J hconj hcard (line F)
  change Nat.card (specialStabilizer J (line F)) = 5 * Nat.card (lineParabolic J) at hs
  rw [card_lineParabolic_four J hcard hconj hJ] at hs
  have hc := (specialStabilizer J (line F)).card_mul_index
  rw [hi, hs] at hc
  norm_num at hc ⊢
  exact hc.symm

/-- The order-divisibility input for the odd-primary covering calculations. -/
theorem card_specialSubgroup_dvd (J : HermitianForm 5 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4)
    (hJ : J.form = 1) :
    Nat.card J.specialSubgroup ∣ 2^20 * 3^2 * 5^5 * 13 * 17 * 41 :=
  (card_specialSubgroup_four J hcard hconj hJ).dvd

/-- Discharge the ambient-order premise of the actual three-primary sections. -/
theorem three_primeLocalSections_four (J : HermitianForm 5 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4)
    (hJ : J.form = 1) : PrimeLocalSections J 3 :=
  three_primeLocalSections_of_card_dvd J hcard hconj hJ
    (card_specialSubgroup_dvd J hcard hconj hJ)

/-- Discharge the ambient-order premise of the actual seventeen-primary sections. -/
theorem seventeen_primeLocalSections_four (J : HermitianForm 5 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4)
    (hJ : J.form = 1) : PrimeLocalSections J 17 :=
  seventeen_primeLocalSections_of_card_dvd J
    (card_specialSubgroup_dvd J hcard hconj hJ)
end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.OddSections
