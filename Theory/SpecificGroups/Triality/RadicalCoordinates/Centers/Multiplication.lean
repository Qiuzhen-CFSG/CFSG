module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers.Coordinates
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection.SumExchange
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection.NonsumCommute


/-!
# Multiplication in the actual triality arms radical

Collect the nine supported canonical Geck curves in the published root order.
The only contributing pairs are (3,10), (4,8), (5,9), and (6,7), all with
sum the highest root 11. The proved sum exchanges and non-sum commutation
laws therefore collect the product without further matrix certificates.
The three orbit-pair corrections give the published trace pairing, with its
Frobenius shift fixed by the actual graph-field expansion. The singleton
pair contributes the product of the two fixed-field parameters.

Transport through the existing fixed-root and faithful descent equivalences
gives the multiplication, square, and commutator formulas in the genuine
carrier. Characteristic two makes the commutator scalar the sum of the two
cocycles. No lower bound beyond a positive binary exponent is used, so all
formulas include q = 2.

Source: GLS3 2.4.5 and §2.6 (`refs/KGroup/GLS3/chapter2.tex`);
Aschbacher–Smith F.1.11–12 (`refs/quasithin.pdf`, printed pp.262–264).
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.PositiveCoordinates
open Triality.Standard.PositiveCoordinates.SumExchangeData
noncomputable section
namespace Triality.Standard.RadicalCoordinates.Centers

private theorem arms_sum_only_highest : ∀ i j k : Fin 12,
    3 ≤ j → j < i → (i, j, k) ∈ sumTriples → k = 11 := by
  decide +kernel

private theorem arms_curve_exchange (P : Parameters) (hp : P.prime = 2)
    (i j : Fin 12) (hj : 3 ≤ j) (hij : j < i) (a b : ExtensionField P) :
    curve P i a * curve P j b = curve P j b * curve P i a *
      curve P 11 (if (i,j,11) ∈ sumTriples then a * b else 0) := by
  by_cases h : (i,j,11) ∈ sumTriples
  · rw [if_pos h]
    have hs : SumExchange P := by
      obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
      exact sumExchange_binary n hn
    exact hs i j 11 ((root_sum_iff i j 11).mpr ((mem_sumTriples_iff i j 11).mp h)) a b
  · rw [if_neg h, curve_zero, mul_one]
    apply (nonsumCommute_parameters P i j (ne_of_gt hij) _ a b).eq
    rintro ⟨k, hk⟩
    have hm := (mem_sumTriples_iff i j k).mpr ((root_sum_iff i j k).mp hk)
    have he := arms_sum_only_highest i j k hj hij hm
    exact h (he ▸ hm)

private theorem arms_curve_exchange_tail (P : Parameters) (hp : P.prime = 2)
    (i j : Fin 12) (hj : 3 ≤ j) (hij : j < i) (a b : ExtensionField P)
    (g : SplitGroup P) :
    curve P i a * (curve P j b * g) =
      curve P j b * (curve P i a * (curve P 11
        (if (i,j,11) ∈ sumTriples then a * b else 0) * g)) := by
  rw [← mul_assoc, arms_curve_exchange P hp i j hj hij]
  simp only [mul_assoc]

private theorem arms_curve_add_tail (P : Parameters) (i : Fin 12)
    (a b : ExtensionField P) (g : SplitGroup P) :
    curve P i a * (curve P i b * g) = curve P i (a + b) * g := by
  rw [← mul_assoc, ← curve_add]

/-- Collecting the actual split Geck product gives the published scalar cocycle. -/
theorem armsProduct_multiply (P : Parameters) (hp : P.prime = 2) (v w : ArmsParameters P) :
    armsProduct P (armsMultiply P v w) = armsProduct P v * armsProduct P w := by
  symm
  simp only [armsProduct, armsMultiply, orderedProduct, expand, extendOrbit,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    Matrix.cons_val_zero, Matrix.cons_val_succ,
    Pi.add_apply, Subfield.coe_add, map_zero, curve_zero, one_mul, mul_one]
  simp only [mul_assoc]
  simp [arms_curve_exchange_tail P hp, arms_curve_add_tail,
    ← curve_add, sumTriples, armsCocycle, armsPairing_coe, -curve_simple,
    -fieldFrobenius_apply]
  congr 1
  ring

/-- The multiplication law survives the faithful descent to the genuine carrier. -/
theorem armsEquiv_multiply (P : Parameters) (hp : P.prime = 2)
    (v w : ArmsParameters P) :
    armsEquiv P hp (armsMultiply P v w) = armsEquiv P hp v * armsEquiv P hp w := by
  let f : ArmsParameters P → (rootSubgroup P .arms).comap (fixedSubgroup P).subtype :=
    fun v => fixedRootEquiv P hp .arms (rootOrbitEquiv P .arms v)
  have h : f (armsMultiply P v w) = f v * f w :=
    Subtype.ext (Subtype.ext (armsProduct_multiply P hp v w))
  exact (congrArg (descendedRootEquiv P hp .arms) h).trans
    ((descendedRootEquiv P hp .arms).map_mul (f v) (f w))

/-- Squares have only the highest-root coordinate, given by the diagonal cocycle. -/
theorem armsEquiv_square (P : Parameters) (hp : P.prime = 2) (v : ArmsParameters P) :
    (armsEquiv P hp v) ^ 2 =
      armsEquiv P hp (centralParameters P (armsCocycle P v v)) := by
  rw [pow_two, ← armsEquiv_multiply, armsMultiply_self P hp]

private theorem armsMultiply_commutator_left (P : Parameters) (hp : P.prime = 2)
    (v w : ArmsParameters P) :
    armsMultiply P (centralParameters P (armsCommutator P v w)) (armsMultiply P w v) =
      armsMultiply P v w := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  have hz (z : fixedField P) (u : ArmsParameters P) :
      armsCocycle P (centralParameters P z) u = 0 := by
    simp [armsCocycle, centralParameters]
  apply Prod.ext
  · change 0 + (w.1 + v.1) = v.1 + w.1
    rw [zero_add, add_comm]
  · funext i
    fin_cases i
    · change 0 + (w.2 0 + v.2 0) = v.2 0 + w.2 0
      rw [zero_add, add_comm]
    · change 0 + (w.2 1 + v.2 1) = v.2 1 + w.2 1
      rw [zero_add, add_comm]
    · change armsCommutator P v w + (w.2 2 + v.2 2 + armsCocycle P w v) +
        armsCocycle P (centralParameters P (armsCommutator P v w)) (armsMultiply P w v) =
          v.2 2 + w.2 2 + armsCocycle P v w
      rw [hz, add_zero, armsCommutator]
      calc
        (armsCocycle P v w + armsCocycle P w v) +
            (w.2 2 + v.2 2 + armsCocycle P w v) =
            (v.2 2 + w.2 2 + armsCocycle P v w) +
              (armsCocycle P w v + armsCocycle P w v) := by abel
        _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]

open scoped commutatorElement

/-- The actual group commutator is the highest-root element with the alternating
trace scalar. This uses Lean's convention `x * y * x⁻¹ * y⁻¹`. -/
theorem armsEquiv_commutator (P : Parameters) (hp : P.prime = 2)
    (v w : ArmsParameters P) :
    ⁅armsEquiv P hp v, armsEquiv P hp w⁆ =
      armsEquiv P hp (centralParameters P (armsCommutator P v w)) := by
  have he : armsEquiv P hp v * armsEquiv P hp w =
      armsEquiv P hp (centralParameters P (armsCommutator P v w)) *
        (armsEquiv P hp w * armsEquiv P hp v) := by
    rw [← armsEquiv_multiply, ← armsEquiv_multiply, ← armsEquiv_multiply,
      armsMultiply_commutator_left P hp]
  rw [commutatorElement_def, he]
  group

end Triality.Standard.RadicalCoordinates.Centers
