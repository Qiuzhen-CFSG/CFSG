module
public import Theory.GroupTheory.PGroup.NormalEightCriticalSubgroup
public import Theory.GroupTheory.InvolutionTransfer
public import Theory.GroupTheory.ElementaryEightNormalizerFusion
public import Theory.GroupTheory.PGroup.NormalEightIndexTwoFixedElements
public import Theory.GroupTheory.PGroup.HomocyclicIndexTwoElementaryGeometry
public import Theory.GroupTheory.PGroup.NormalEightAbelianCriticalAction
public import Theory.GroupTheory.SylowPGroupAutomizer

/-!
# Transfer and the abelian index-two fusion branch

An involution in a Sylow two-subgroup of a nonsolvable simple group has
an ambient conjugate in each index-two subgroup. When that subgroup is
critical and the Sylow group has central omega four and no normal
elementary eight, the conjugate is central in the Sylow group.

The elementary-eight normalizer obstruction therefore places every
involution in the critical subgroup. The fixed-element theorem supplies
outside elementary centralizers of order eight; every elementary eight is
self-centralizing with normalizer of order 32. The required homocyclic
structure and abstract order-three automorphism follow from the nontrivial
outer normalizer action. The final theorem discharges all these local
premises and uses ambient transfer and fusion to exclude outside involutions.

Source context: MacWilliams, Trans. AMS 150 (1970), DOI
10.1090/S0002-9947-1970-0276324-3; Janko–Thompson, Math. Z. 113 (1970),
Theorem 1.3, printed p.386. The transfer and elementary-eight automizer
steps use the independently proved Theory interfaces.
-/

open Subgroup

namespace Stellmacher.Recognition.NormalEightMacWilliamsAbelianIndexTwo

private theorem no_normal_index_two
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (K : Subgroup G) (hK : K.Normal) : K.index ≠ 2 := by
  intro hi
  rcases hK.eq_bot_or_eq_top with hbot | htop
  · have hcard : Nat.card G = 2 := by simpa only [hbot, index_bot] using hi
    let : IsCyclic G := isCyclic_of_prime_card hcard
    let : CommGroup G := IsCyclic.commGroup
    exact hns (Group.isSolvable_of_comm (fun a b => mul_comm a b))
  · simp only [htop, index_top] at hi
    omega

/-- Transfer places a conjugate of every Sylow involution in the central
four contained in the critical subgroup. -/
public theorem exists_isConj_critical_center
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (C : Subgroup S) (hC : IsCriticalPSubgroup 2 C) (hi : C.index = 2)
    (x : S) (hx : orderOf x = 2) :
    ∃ z : S, z ∈ C ∧ z ∈ center S ∧ orderOf z = 2 ∧ IsConj (x : G) (z : G) := by
  obtain ⟨z, hconj, hzC⟩ := S.exists_isConj_mem_of_index_two
    (no_normal_index_two hns) C hi x hx
  have hz : orderOf z = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    rw [← Subgroup.orderOf_coe, ← hg]
    change orderOf ((MulAut.conj g) (x : G)) = 2
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hx]
  have hz2 : z ^ 2 = 1 := by simpa only [hz] using pow_orderOf_eq_one z
  have hzc := map_subtype_le _ (hC.mem_omega_center_of_square_eq_one hno hZ hzC hz2)
  exact ⟨z, hzC, hzc, hz, hconj⟩

/-- The elementary-eight local geometry discharges the ambient fusion step.
The structural hypotheses supplying this geometry are kept explicit. -/
public theorem involution_mem_of_elementary_eight_geometry
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (C : Subgroup S) (hC : IsCriticalPSubgroup 2 C) (hi : C.index = 2)
    (hself : ∀ E : Subgroup S, IsElementaryAbelian 2 E → Nat.card E = 8 →
      centralizer (E : Set S) = E)
    (hcount : ∀ E : Subgroup S, IsElementaryAbelian 2 E → Nat.card E = 8 →
      Nat.card (normalizer (E : Set S)) = 32)
    (hout : ∀ t : S, orderOf t = 2 → t ∉ C →
      IsElementaryAbelian 2 (centralizer ({t} : Set S)) ∧
        Nat.card (centralizer ({t} : Set S)) = 8) :
    ∀ x : S, orderOf x = 2 → x ∈ C := by
  intro x hx
  by_contra hxc
  obtain ⟨z, _, hzc, _, hconj⟩ := exists_isConj_critical_center hns S hno hZ C hC hi x hx
  obtain ⟨helem, hcard⟩ := hout x hx hxc
  let : IsElementaryAbelian 2 (centralizer ({x} : Set S)) := helem
  exact S.not_isConj_of_elementary_eight_centralizer_geometry hself hcount z x hzc
    (centralizer ({x} : Set S)) rfl hcard hconj.symm

/-- Homocyclic coordinates and a free cubic action supply the local geometry
needed by the ambient fusion obstruction. -/
public theorem involution_mem_of_homocyclic_index_two
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (C : Subgroup S) (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hi : C.index = 2) (n : ℕ) (hn : 2 ≤ n)
    (e : C ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (a : MulAut S) (ha : orderOf a = 3)
    (hfree : ∀ c ∈ C, a c = c → c = 1) :
    ∀ x : S, orderOf x = 2 → x ∈ C := by
  let : C.Characteristic := hC.characteristic
  have hcentral : ∀ c ∈ C, c ^ 2 = 1 → c ∈ center S := by
    intro c hc hs
    exact map_subtype_le _ (hC.mem_omega_center_of_square_eq_one hno hZ hc hs)
  have hfixed := IsCriticalPSubgroup.fixed_square_eq_one_of_index_two
    S.isPGroup' C hC hi hno hZ n hn e a ha hfree
  apply involution_mem_of_elementary_eight_geometry hns S hno hZ C hC hi
  · intro E hE hcard
    let : IsElementaryAbelian 2 E := hE
    exact HomocyclicIndexTwo.elementary_eight_self_centralizing
      C hi hcentral hfixed n hn e E hcard
  · intro E hE hcard
    let : IsElementaryAbelian 2 E := hE
    exact HomocyclicIndexTwo.elementary_eight_normalizer_card
      C hi hcentral hfixed n hn e E hcard
  · exact HomocyclicIndexTwo.centralizer_geometry C hi hcentral hfixed n hn e

/-- In the abelian index-two critical case, nontrivial outer normalizer action
forces every Sylow involution into the critical subgroup. -/
public theorem involution_mem_of_index_two
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hnorm : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G))
    (C : Subgroup S) (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hi : C.index = 2) : ∀ x : S, orderOf x = 2 → x ∈ C := by
  have hAut := S.not_isPGroup_mulAut_of_normalizer_ne_sup_centralizer hnorm
  obtain ⟨n, hn, ⟨e⟩⟩ :=
    hC.homocyclic_large_of_not_isPGroup_mulAut S.isPGroup' hAut hnonab hno hZ
  obtain ⟨a, ha, hfree⟩ := hC.exists_order_three_free_on_critical S.isPGroup' hAut
    (hC.card_omega_one_eq_four hno hZ)
  exact involution_mem_of_homocyclic_index_two hns S hno hZ C hC hi n hn e a ha hfree

/-- Consequently every involution is central in the Sylow subgroup. -/
public theorem involution_mem_center_of_index_two
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hnorm : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G))
    (C : Subgroup S) (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hi : C.index = 2) : ∀ x : S, orderOf x = 2 → x ∈ center S := by
  intro x hx
  have hmem := involution_mem_of_index_two hns S hnonab hZ hno hnorm C hC hi x hx
  exact map_subtype_le _ (hC.mem_omega_center_of_square_eq_one hno hZ hmem
    (by simpa only [hx] using pow_orderOf_eq_one x))

end Stellmacher.Recognition.NormalEightMacWilliamsAbelianIndexTwo
