module

public import Theory.SpecificGroups.Janko3.Model.ThreeRank.ElementaryGenerators
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# A concrete lower bound for the ordinary three-rank of J3

Three certified commuting permutations generate an elementary abelian subgroup
of order 27 in the actual degree-6156 carrier. Independence is checked on the
image of one letter, and the cardinality follows by adjoining two independent
cyclic factors. This is the lower bound in GLS, volume 3, Table 5.6.1 and the
J3 case of Aschbacher–Smith A.2.19, printed p. 41 (PDF p. 52).

The source upper bound uses the first omega subgroup of a Sylow three-subgroup
(Table 5.3h, note 2). It is not asserted here until that local structure and the
required Sylow order have been certified.
-/

namespace Sporadic.Janko3
noncomputable section
open Subgroup ThreeRankCertificate
open scoped Pointwise
set_option maxRecDepth 100000

private theorem y_not_mem_x : y ∉ zpowers x := by
  rw [mem_zpowers_iff_mem_range_orderOf, x_order]
  intro h
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
  have hh : ∀ i : Fin 3,
      (y : Equiv.Perm (Fin 6156)) 0 ≠ ((x : Equiv.Perm (Fin 6156)) ^ i.val) 0 := by
    decide +kernel
  exact hh ⟨i, Finset.mem_range.mp hi⟩ (congrArg (fun g : Model => (g : Equiv.Perm (Fin 6156)) 0) he).symm

private theorem x_centralizes_y : zpowers x ≤ centralizer ({y} : Set Model) :=
  zpowers_le.mpr (mem_centralizer_singleton_iff.mpr x_commute_y.eq)

private theorem y_normalizes_x : zpowers y ≤ normalizer (zpowers x : Set Model) := by
  apply le_trans _ (centralizer_le_normalizer _)
  apply zpowers_le.mpr
  intro u hu
  exact mem_centralizer_singleton_iff.mp (x_centralizes_y hu)

private theorem xy_properties : IsElementaryAbelian 3 (zpowers x ⊔ zpowers y : Subgroup Model) ∧
    Nat.card (zpowers x ⊔ zpowers y : Subgroup Model) = 3 ^ 2 := by
  let : IsElementaryAbelian 3 (zpowers x) := IsElementaryAbelian.zpowers_of_pow_eq_one x_cube
  exact IsElementaryAbelian.fixed_join_card (zpowers x) y y_order
    ((zpowers x).disjoint_zpowers_of_prime_order_not_mem y y_order y_not_mem_x)
    x_centralizes_y (by rw [Nat.card_zpowers, x_order]; norm_num)

private theorem z_not_mem_xy : z ∉ (zpowers x ⊔ zpowers y : Subgroup Model) := by
  intro h
  have hp : z ∈ (zpowers x : Set Model) * (zpowers y : Set Model) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ y_normalizes_x]
    exact h
  obtain ⟨u, hu, v, hv, he⟩ := hp
  change u ∈ zpowers x at hu
  change v ∈ zpowers y at hv
  rw [mem_zpowers_iff_mem_range_orderOf, x_order] at hu
  rw [mem_zpowers_iff_mem_range_orderOf, y_order] at hv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
  have hh : ∀ i j : Fin 3, (z : Equiv.Perm (Fin 6156)) 0 ≠
      ((x : Equiv.Perm (Fin 6156)) ^ i.val * (y : Equiv.Perm (Fin 6156)) ^ j.val) 0 := by
    decide +kernel
  exact hh ⟨i, Finset.mem_range.mp hi⟩ ⟨j, Finset.mem_range.mp hj⟩
    (congrArg (fun g : Model => (g : Equiv.Perm (Fin 6156)) 0) he).symm

/-- A concrete order-27 elementary subgroup of the degree-6156 J3 model. -/
@[expose] public def j3ThreeElementary : Subgroup Model :=
  (zpowers x ⊔ zpowers y) ⊔ zpowers z

private theorem j3ThreeElementary_properties : IsElementaryAbelian 3 j3ThreeElementary ∧
    Nat.card j3ThreeElementary = 3 ^ 3 := by
  let : IsElementaryAbelian 3 (zpowers x ⊔ zpowers y : Subgroup Model) := xy_properties.1
  exact IsElementaryAbelian.fixed_join_card (zpowers x ⊔ zpowers y) z z_order
    ((zpowers x ⊔ zpowers y).disjoint_zpowers_of_prime_order_not_mem z z_order z_not_mem_xy)
    (sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr x_commute_z.eq))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr y_commute_z.eq))) xy_properties.2

/-- The concrete witness is elementary abelian, without an order assumption on J3. -/
public instance j3ThreeElementary_elementary : IsElementaryAbelian 3 j3ThreeElementary :=
  j3ThreeElementary_properties.1

/-- The concrete witness has precisely 27 elements. -/
public theorem j3ThreeElementary_card : Nat.card j3ThreeElementary = 3 ^ 3 :=
  j3ThreeElementary_properties.2

/-- The unconditional lower bound for the ordinary three-rank of the actual J3 model. -/
public theorem j3_primeRank_three_ge : 3 ≤ primeRank 3 Model :=
  IsElementaryAbelian.primeRank_ge_of_card j3ThreeElementary j3ThreeElementary_card

end
end Sporadic.Janko3
