module

public import ABG.Recognition.ThreeLinearCentralizerFixedSpaces
public import ABG.Recognition.ThreeLinearMConstruction
public import Theory.GroupTheory.SpecificGroups.DihedralThreeSquare

/-!
# The fixed-space calculation for Wong's order-thirty-six subgroup

An actual S₃ × S₃ subgroup has fifteen involutions, twelve elements of order
six, and eight elements of order three. Equation (14) makes its character
sum `84 + 3n`, where `n ≤ 8` counts the eligible order-three elements.
Integrality of the average forces `n = 8` and fixed-space dimension three.
For an overgroup of the transported Borel, the existing centralizer and
shared-subgroup dimensions then give a proper generated subgroup.

The Sylow-three construction supplies this overgroup of the specified Borel.
The final assembly retains the original representation and constructs the
configuration from the original recognition hypotheses.
Source: Wong (1964), Appendix (b), pp.109–110, equation (14).
-/

namespace ABG.ThreeLinearLocalData
open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite

variable {G : Type*} [Group G] [Finite G] (c : ThreeLinearLocalData G)

private theorem sum_indicator (H : Type*) [Fintype H] (p : H → Prop) [DecidablePred p]
    (a : ℂ) : (∑ x : H, if p x then a else 0) =
      (Nat.card {x : H // p x} : ℂ) * a := by
  classical
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The fifteen involutions and twelve order-six elements contribute 72;
the identity contributes twelve and each eligible element contributes three. -/
public theorem order36_character_sum (M : Subgroup G)
    (hM : Nat.card M = 36)
    (h2 : Nat.card {x : M // orderOf x = 2} = 15)
    (h6 : Nat.card {x : M // orderOf x = 6} = 12) :
    ∑ x : M, c.decomposition.χ 5 (x : G) =
      84 + 3 * (Nat.card {x : M // ThreeLinearPlane.IsPointElement G (x : G)} : ℂ) := by
  classical
  let : Fintype M := Fintype.ofFinite M
  have hv (x : M) : c.decomposition.χ 5 (x : G) =
      (if x = 1 then 12 else 0) + (if orderOf x = 2 then 4 else 0) +
      (if ThreeLinearPlane.IsPointElement G (x : G) then 3 else 0) +
      (if orderOf x = 6 then 1 else 0) := by
    have h13 : orderOf (x : G) ≠ 13 := by
      have hd := orderOf_dvd_natCard x
      rw [hM] at hd
      intro h
      rw [← Subgroup.orderOf_coe, h] at hd
      norm_num at hd
    rw [c.sixth_values, if_neg h13]
    by_cases h1 : x = 1
    · subst x
      simp [ThreeLinearPlane.IsPointElement]
    · have h1G : (x : G) ≠ 1 := by simpa using h1
      simp only [h1, h1G, if_false, Subgroup.orderOf_coe, zero_add]
      by_cases h2x : orderOf x = 2
      · have hp : ¬ ThreeLinearPlane.IsPointElement G (x : G) := by
          intro hp
          have := hp.1
          rw [Subgroup.orderOf_coe, h2x] at this
          norm_num at this
        simp [h2x, hp]
      · by_cases hp : ThreeLinearPlane.IsPointElement G (x : G)
        · have h3 : orderOf x = 3 := (Subgroup.orderOf_coe x).symm.trans hp.1
          simp [h3, hp]
        · simp [h2x, hp]
  simp_rw [hv]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [sum_indicator M (fun x => x = 1), sum_indicator M (fun x => orderOf x = 2),
    sum_indicator M (fun x => ThreeLinearPlane.IsPointElement G (x : G)),
    sum_indicator M (fun x => orderOf x = 6), h2, h6]
  simp
  ring

/-- The actual order-36 census forces fixed-space dimension three. -/
public theorem order36_fixed_dimension (M : Subgroup G)
    (hM : Nat.card M = 36)
    (h2 : Nat.card {x : M // orderOf x = 2} = 15)
    (h3 : Nat.card {x : M // orderOf x = 3} = 8)
    (h6 : Nat.card {x : M // orderOf x = 6} = 12) :
    Nat.card {x : M // ThreeLinearPlane.IsPointElement G (x : G)} = 8 ∧
    Module.finrank ℂ (Representation.invariants
      (c.sixthRepresentation.comp M.subtype)) = 3 := by
  have hle : Nat.card {x : M // ThreeLinearPlane.IsPointElement G (x : G)} ≤ 8 := by
    rw [← h3]
    apply Nat.card_le_card_of_injective
      (fun x => (⟨x.val, (Subgroup.orderOf_coe x.val).symm.trans x.property.1⟩ :
        {x : M // orderOf x = 3}))
    intro x y h
    exact Subtype.ext (congrArg (fun z : {x : M // orderOf x = 3} => z.val) h)
  exact c.toThreeLinearCharacterData.order36_fixed_dimension M hM _ hle
    (c.order36_character_sum M hM h2 h6)

/-- A concrete S₃ × S₃ overgroup of the shared Borel supplies all three
fixed dimensions and the proper join required in Wong's argument. -/
public theorem configuration_of_dihedral_square (M : Subgroup G)
    (e : M ≃* (DihedralGroup 3 × DihedralGroup 3))
    (hTM : c.sharedSubgroup ≤ M) :
    Nat.card M = 36 ∧ Nat.card c.sharedSubgroup = 12 ∧
    c.sharedSubgroup ≤ Subgroup.centralizer ({c.involution} : Set G) ∧
    Module.finrank ℂ (Representation.invariants (c.sixthRepresentation.comp M.subtype)) = 3 ∧
    Module.finrank ℂ (Representation.invariants (c.sixthRepresentation.comp
      (Subgroup.centralizer ({c.involution} : Set G)).subtype)) = 2 ∧
    Module.finrank ℂ (Representation.invariants
      (c.sixthRepresentation.comp c.sharedSubgroup.subtype)) = 4 ∧
    M ⊔ Subgroup.centralizer ({c.involution} : Set G) ≠ ⊤ := by
  obtain ⟨hM, h2, h3, h6⟩ := DihedralGroup.square_three_census e
  have hm := (c.order36_fixed_dimension M hM h2 h3 h6).2
  exact ⟨hM, c.sharedSubgroup_card, c.sharedSubgroup_le_centralizer,
    hm, c.centralizer_fixed_dimension, c.sharedSubgroup_fixed_dimension,
    c.toThreeLinearCharacterData.sup_ne_top_of_fixed_dimensions M _ c.sharedSubgroup
      hTM c.sharedSubgroup_le_centralizer hm c.centralizer_fixed_dimension
      c.sharedSubgroup_fixed_dimension⟩

/-- Wong's actual subgroups `M`, `C_G(τ)`, and the specified shared Borel `T`,
with the fixed spaces of the original degree-twelve representation. -/
public structure MSubgroupConfiguration (M : Subgroup G) : Prop where
  shared_le : c.sharedSubgroup ≤ M
  dihedral_square : Nonempty (M ≃* (DihedralGroup 3 × DihedralGroup 3))
  card : Nat.card M = 36
  shared_card : Nat.card c.sharedSubgroup = 12
  centralizer_card : Nat.card (Subgroup.centralizer ({c.involution} : Set G)) = 48
  shared_le_centralizer : c.sharedSubgroup ≤ Subgroup.centralizer ({c.involution} : Set G)
  fixed_dimension : Module.finrank ℂ (Representation.invariants
    (c.sixthRepresentation.comp M.subtype)) = 3
  centralizer_fixed_dimension : Module.finrank ℂ (Representation.invariants
    (c.sixthRepresentation.comp (Subgroup.centralizer ({c.involution} : Set G)).subtype)) = 2
  shared_fixed_dimension : Module.finrank ℂ (Representation.invariants
    (c.sixthRepresentation.comp c.sharedSubgroup.subtype)) = 4
  sup_ne_top : M ⊔ Subgroup.centralizer ({c.involution} : Set G) ≠ ⊤

/-- The Sylow-three construction and equation (14) produce Wong's subgroup
and all three fixed dimensions, without assuming an overgroup or a census. -/
public theorem exists_mSubgroup_configuration
    (hC : ∀ t : G, orderOf t = 2 →
      Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1) :
    ∃ M : Subgroup G, c.MSubgroupConfiguration M := by
  obtain ⟨M, hTM, ⟨e⟩⟩ := c.exists_dihedral_square hC
  obtain ⟨hM, hT, hTC, hfixM, hfixC, hfixT, hproper⟩ :=
    c.configuration_of_dihedral_square M e hTM
  exact ⟨M, ⟨hTM, ⟨e⟩, hM, hT, c.centralizer_card, hTC,
    hfixM, hfixC, hfixT, hproper⟩⟩

end
end ABG.ThreeLinearLocalData

namespace ABG

/-- Wong's order-36 subgroup and shared order-12 subgroup, with fixed-space
dimensions `3`, `2`, and `4`, follow from the original recognition hypotheses. -/
public theorem exists_threeLinearMSubgroup
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S) (hcard : Nat.card S = 16)
    (hC : ∀ t : G, orderOf t = 2 →
      Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1)
    (hG : Nat.card G = 5616) :
    ∃ c : ThreeLinearLocalData G, ∃ M : Subgroup G, c.MSubgroupConfiguration M := by
  obtain ⟨c⟩ := exists_threeLinearLocalData S hS hcard hC hG
  obtain ⟨M, hM⟩ := c.exists_mSubgroup_configuration hC
  exact ⟨c, M, hM⟩

end ABG
