module

public import Theory.GroupTheory.PGroup.NormalEightCriticalSubgroup
public import Theory.GroupTheory.PGroup.AbelianRankTwoHomocyclic
public import Stellmacher.Recognition.NormalEightMacWilliamsAbelianCritical
public import Stellmacher.Recognition.NormalEightMacWilliamsNonabelianCritical

/-!
# MacWilliams involution centrality in the central-omega-four case

In the central-omega-four case without normal elementary eights, a Thompson
critical subgroup has precisely the ambient central omega as its first
omega. Its involutions are central in the Sylow subgroup, and its Frattini
quotient has order at most sixteen. If it is abelian, it is a product of two
nontrivial cyclic two-groups and is self-centralizing.

Choose a critical subgroup and split according to whether it is abelian.
The abelian extension and fusion theorem and the nonabelian critical-center
theorem both centralize every Sylow involution, including those outside the
critical subgroup. Their assembly proves centrality in a nonsolvable simple
ambient group with nontrivial outer Sylow normalizer action. No elementary-rank
bound on the Sylow subgroup is assumed.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3, printed p.386,
quoting MacWilliams, Trans. AMS 150 (1970), DOI
10.1090/S0002-9947-1970-0276324-3.
-/

open Subgroup

namespace Stellmacher.Recognition.NormalEightMacWilliamsCentrality

/-- The characteristic subgroup on which the remaining extension argument
can work already has three central involutions and small Frattini quotient. -/
public theorem exists_critical_subgroup_data
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E) :
    ∃ C : Subgroup S, IsCriticalPSubgroup 2 C ∧
      (omega₁ C (p := 2)).map C.subtype =
        (omega₁ (center S) (p := 2)).map (center S).subtype ∧
      (∀ x : C, x ^ 2 = 1 → (x : S) ∈ center S) ∧
      Nat.card (omega₁ C (p := 2)) = 4 ∧
      Nat.card {x : C // orderOf x = 2} = 3 ∧
      Nat.card (C ⧸ frattini C) ≤ 16 := by
  obtain ⟨C, hC⟩ := S.isPGroup'.exists_criticalPSubgroup
  refine ⟨C, hC, hC.omega_one_map_eq_center hno hZ, ?_,
    hC.card_omega_one_eq_four hno hZ, hC.card_involutions_eq_three hno hZ,
    hC.card_frattini_quotient_le_sixteen_of_no_normal_eight S.isPGroup' hno hZ⟩
  intro x hx
  exact map_subtype_le _ (hC.mem_omega_center_of_square_eq_one hno hZ
    x.property (congrArg Subtype.val hx))

/-- In the abelian branch the critical subgroup is self-centralizing and
has two nontrivial cyclic factors. Characteristicity comes from `hC`. -/
public theorem abelian_critical_subgroup_data
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (C : Subgroup S) (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C] :
    centralizer (C : Set S) = C ∧
      ∃ n m : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ Nonempty
        (C ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ m)))) := by
  refine ⟨?_, (S.isPGroup'.to_subgroup C).equiv_two_cyclic_factors_of_card_omega_one_eq_four
    (hC.card_omega_one_eq_four hno hZ)⟩
  rw [hC.centralizer_eq, center_eq_top, ← MonoidHom.range_eq_map, C.range_subtype]

/-- Every involution is central in the central-four MacWilliams case.
A separate normal elementary four subgroup is unnecessary: the central first
omega already supplies it. -/
public theorem involution_mem_center
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hnorm : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G)) :
    ∀ x : S, orderOf x = 2 → x ∈ center S := by
  obtain ⟨C, hC⟩ := S.isPGroup'.exists_criticalPSubgroup
  by_cases hCab : IsMulCommutative C
  · let := hCab
    exact NormalEightMacWilliamsAbelianCritical.involution_mem_center
      hns S hnonab hZ hno hnorm C hC
  · exact NormalEightMacWilliamsNonabelianCritical.involutions_central_of_nonabelian_critical
      hns S hZ hno hnorm C hC hCab

end Stellmacher.Recognition.NormalEightMacWilliamsCentrality
