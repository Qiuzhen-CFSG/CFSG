module

public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.Threes.LocalModel
public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.Threes.RepresentativeOrders

/-!
# Order-three coverage for the Thompson model

All three designated words have certified order three. For coverage, we use the
concrete subgroup from `ThG1-max6W1`: it suffices to construct
an order-`3^10` subgroup inside it. That subgroup is Sylow in the ambient model
under the proposed ambient order. The two remaining certificates are this
subgroup construction and fusion of the local order-three elements to the
three fixed words.
No local identification or class census is assumed.

Source: the ATLAS Thompson subgroup and class-word programs, documented in
`Threes/source/README.md`.
-/

public section
namespace Thompson.Simplicity
open PrimeCyclicCoverage

/-- Each of the three fixed candidates has exact order three. -/
theorem orderOf_threeRepresentative (i : Fin 3) :
    orderOf (primeRepresentative (ThreeLocal.representativeIndex i)) = 3 := by
  fin_cases i
  · exact orderOf_primeRepresentative_one
  · exact orderOf_primeRepresentative_two
  · exact orderOf_primeRepresentative_three

/-- A subgroup of order `3^10` has index prime to three under the proposed
ambient order. -/
theorem three_not_dvd_index (H : Subgroup Model)
    (hcard : Nat.card Model = 90745943887872000) (hH : Nat.card H = 59049) :
    ¬3 ∣ H.index := by
  intro hd
  have he : 177147 ∣ Nat.card Model := by
    rw [← H.card_mul_index, hH]
    exact Nat.mul_dvd_mul_left 59049 hd
  rw [hcard] at he
  exact (by decide : ¬177147 ∣ 90745943887872000) he

/-- Assemble the two concrete local certificates. This theorem restricts
coverage to indices `1,2,3`; the remaining premises are owned by the subgroup and
fusion certificate modules. -/
theorem three_coverage_of_local_certificates
    (hcard : Nat.card Model = 90745943887872000)
    (hsubgroup : ∃ S : Subgroup Model, S ≤ ThreeLocal.localSubgroup ∧ Nat.card S = 59049)
    (hfusion : ThreeLocal.LocalFusion) :
    ∀ x : Model, orderOf x = 3 →
      ∃ (i : Fin 3) (k : ℕ) (g : Model),
        primeRepresentative (ThreeLocal.representativeIndex i) = g * x ^ k * g⁻¹ := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨S, hle, hS⟩ := hsubgroup
  have hp : IsPGroup 3 S := IsPGroup.of_card (hS.trans (by decide : 59049 = 3 ^ 10))
  let Q : Sylow 3 Model := hp.toSylow (three_not_dvd_index S hcard hS)
  apply prime_cyclic_coverage_of_sylow
    (fun i : Fin 3 => primeRepresentative (ThreeLocal.representativeIndex i)) Q
  intro y hy hord
  exact hfusion y (hle hy) hord

/-- The local certificates imply the parent's coverage interface. -/
theorem covers_three_of_local_certificates
    (hcard : Nat.card Model = 90745943887872000)
    (hsubgroup : ∃ S : Subgroup Model, S ≤ ThreeLocal.localSubgroup ∧ Nat.card S = 59049)
    (hfusion : ThreeLocal.LocalFusion) : CoversPrime primeRepresentative 3 := by
  intro x hx
  obtain ⟨i, k, g, he⟩ := three_coverage_of_local_certificates hcard hsubgroup hfusion x hx
  exact ⟨ThreeLocal.representativeIndex i, k, g, he⟩

end Thompson.Simplicity
