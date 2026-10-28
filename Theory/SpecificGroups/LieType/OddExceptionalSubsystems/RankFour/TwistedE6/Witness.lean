module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.RankFour.TwistedE6.Projection
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.RankFour.E6.Involution

/-!
# An actual involution centralizer in twisted E6

The graph-fixed coroot product h₀h₅ centralizes the signed four-root chart.
Its commutator with the neighboring graph-fixed root pair proves that its
image is nontrivial in the literal defining central quotient. The faithful
chart consequently gives an elementary p-subgroup of order q⁴ inside this
actual involution centralizer.

Source: Aschbacher–Smith A.2.17, printed p.39; GLS3 §2.6.
-/

@[expose] public noncomputable section
open TwistedE6 TwistedE6.FoldedSubsystem Subgroup
open ExceptionalSplit.OddRankFour
namespace TwistedE6.RankFour
variable (p : ℕ) [Fact p.Prime] (m : ℕ)

theorem actor_zero_native :
    ambientInclusion p m (foldedSignActor p m 0) =
      (E6.involution (CoefficientField p m)).val := by
  rw [foldedSignActor_coroot]
  rfl

theorem folded_neighbor_native :
    ambientInclusion p m (foldedRoot p m true 1 1) =
      (simpleRoot (CoefficientField p m) true 1 1 *
        simpleRoot (CoefficientField p m) true 4 1).val := by
  rw [foldedRoot_ambient]
  rfl

theorem involution_ne_one (hp2 : p ≠ 2) : involution p m ≠ 1 := by
  intro hz
  have hz' : foldedSignActor p m 0 ∈ center (definingCharacteristicSubgroup p m) :=
    (toModel_eq_one p m _).mp hz
  have hc := mem_center_iff.mp hz' (foldedRoot p m true 1 1)
  apply E6.involution_not_commute_folded (CoefficientField p m)
    (coefficient_two_ne_zero p m hp2)
  change _ * _ = _ * _
  apply Subtype.ext
  have h := congrArg (ambientInclusion p m) hc.symm
  simpa only [map_mul,actor_zero_native,folded_neighbor_native,Subgroup.coe_mul] using h

theorem involution_order (hp2 : p ≠ 2) : orderOf (involution p m) = 2 :=
  orderOf_eq_prime (involution_square p m) (involution_ne_one p m hp2)

theorem foldedSignActor_chart (a : Parameters p m) :
    Commute (foldedSignActor p m 0) (chartCover p m a) := by
  change _ * _ = _ * _
  apply ambientInclusion_injective p m
  rw [map_mul,map_mul,actor_zero_native,chartCover_native]
  exact congrArg Subtype.val (E6.involution_chart (CoefficientField p m) (nativeParameters p m a)).eq

theorem involution_chart (a : Parameters p m) :
    Commute (involution p m) (chartModel p m a) :=
  (foldedSignActor_chart p m a).map (toModel p m)

def chartCentralizer : Parameters p m →* centralizer ({involution p m} : Set (Model p m)) :=
  (chartModel p m).codRestrict _ (by
    intro a
    apply mem_centralizer_singleton_iff.mpr
    exact (involution_chart p m a).symm.eq)

theorem chartCentralizer_injective (hp2 : p ≠ 2) : Function.Injective (chartCentralizer p m) := by
  intro a b hab
  exact chartModel_injective p m hp2 (congrArg Subtype.val hab)

theorem exists_elementary_four_involution_centralizer (hp2 : p ≠ 2) :
    ∃ z : Model p m, orderOf z = 2 ∧
      ∃ (A : Type) (_ : Group A) (_ : Finite A) (_ : IsElementaryAbelian p A),
        Nat.card A = parameter p m ^ 4 ∧
          ∃ j : A →* centralizer ({z} : Set (Model p m)), Function.Injective j :=
  ⟨involution p m,involution_order p m hp2,Parameters p m,
    inferInstance,inferInstance,inferInstance,parameters_card p m,
    chartCentralizer p m,chartCentralizer_injective p m hp2⟩

end TwistedE6.RankFour
