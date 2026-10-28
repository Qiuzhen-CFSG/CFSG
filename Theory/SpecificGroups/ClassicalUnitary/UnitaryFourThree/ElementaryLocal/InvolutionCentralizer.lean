module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.InvolutionCentralizer.Trace
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.InvolutionCentralizer.RepresentativeBound
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.TwoLocal.InvolutionTransport
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Coset.Card

/-!
# Involution-centralizer three-part bound for PSU₄(3)

The imported trace theorem is unconditional for the actual projective SU
image over `FiniteField.Nine`. It supplies the trace hypothesis of the unitary
eigenbasis construction, which identifies every involution centralizer with
the full projective centralizer of `diag(-1,-1,1,1)`. The latter has order
dividing `2 * 96²`, so its order is not divisible by 27.

The reduction below chooses the nonidentity element of a subgroup of order
two and applies centralizer containment and Lagrange's theorem. The final
theorem discharges both geometric inputs. Throughout, the full projective
centralizer retains lifts that anticommute with the standard involution,
as well as those that commute, and the SU projection retains its scalar kernel.

Source: Aschbacher–Smith, Theorem 0.1.2(4), printed p.4 of `refs/quasithin.pdf`,
restated as Theorem 0.1.1(4) on printed p.482; unitary conventions in GLS3,
chapter 2, §2.7.
-/

namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.InvolutionCentralizer

/-- Actual centralizer equivalences and a representative bound suffice for order-two subgroups. -/
public theorem centralizer_three_part_of_involution_models
    {D : Type*} [Group D]
    (hmodels : ∀ z : Carrier 4, orderOf z = 2 →
      Nonempty (Subgroup.centralizer ({z} : Set (Carrier 4)) ≃* D))
    (hD : ¬ 3 ^ 3 ∣ Nat.card D)
    (A : Subgroup (Carrier 4)) (hA : Nat.card A = 2) :
    ¬ 3 ^ 3 ∣ Nat.card (Subgroup.centralizer (A : Set (Carrier 4))) := by
  obtain ⟨a, hane, _⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  have hsq : (a : Carrier 4) ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := a)
    rw [hA] at h
    exact congrArg Subtype.val h
  have hne : (a : Carrier 4) ≠ 1 := fun h => hane (Subtype.ext h)
  obtain ⟨e⟩ := hmodels a (orderOf_eq_prime hsq hne)
  have hle : Subgroup.centralizer (A : Set (Carrier 4)) ≤
      Subgroup.centralizer ({(a : Carrier 4)} : Set (Carrier 4)) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr a.property)
  intro hdiv
  apply hD
  rw [← Nat.card_congr e.toEquiv]
  exact hdiv.trans (Subgroup.card_dvd_of_le hle)

/-- In the actual PSU₄(3) image, the centralizer of every subgroup of order two
has three-part at most nine. No subgroup classification hypotheses are needed. -/
public theorem centralizer_three_part_of_card_eq_two
    (A : Subgroup (Carrier 4)) (hA : Nat.card A = 2) :
    ¬ 3 ^ 3 ∣ Nat.card (Subgroup.centralizer (A : Set (Carrier 4))) :=
  centralizer_three_part_of_involution_models
    (TwoLocal.centralizer_models_of_trace_zero trace_eq_zero_of_projective_involution)
    TwoLocal.standardCentralizer_three_part A hA

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.InvolutionCentralizer
