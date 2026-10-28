module
public import Theory.GroupTheory.QuaternionCentralProductCenter
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.Basic

/-!
# Every elementary eight in a quaternion central product is self-centralizing

For two commuting quaternion subgroups whose intersection has order two,
every elementary abelian subgroup of order eight in their join is
self-centralizing inside the join. The subgroup need not come with a chosen
diagonal parametrization or a compatible action on the quaternion factors.

Every square-one element of a quaternion group is central. Thus the elementary
subgroup intersects either quaternion factor inside their shared center of
order two. The normalized product formula, together with the join order
thirty-two, forces both intersections to have order two and shows that the
elementary subgroup joined with either factor is the whole central product.
A centralizing element can therefore be written as an elementary element times
an element of one quaternion factor. The latter centralizes the elementary
subgroup and the other quaternion factor, hence the whole product; its
membership in the shared center puts it back in the elementary subgroup.

This is the intrinsic maximal elementary subgroup calculation used in
Stellmacher (9.1), Journal of Algebra 190 (1997), p.48; see
`refs/latex/stellmacher-n-group.tex`. Only Mathlib and reusable Theory
prerequisites are used.
-/

open scoped Pointwise
namespace Subgroup

private theorem quaternion_square_one_central : ∀ x : QuaternionGroup 2,
    x ^ 2 = 1 → ∀ y, y * x = x * y := by decide

private theorem inf_le_shared_center_of_elementary
    {G : Type*} [Group G] [Finite G] (B C U : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    [IsElementaryAbelian 2 U] : U ⊓ B ≤ B ⊓ C := by
  obtain ⟨e⟩ := hB
  rw [intersection_eq_factor_center B C ⟨e⟩ hinter hcomm]
  intro x hx
  refine ⟨⟨x, hx.2⟩, mem_center_iff.mpr ?_, rfl⟩
  intro y
  apply e.injective
  simp only [map_mul]
  apply quaternion_square_one_central
  rw [← map_pow]
  have hx2 : (⟨x, hx.2⟩ : B) ^ 2 = 1 :=
    Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx.1)
  rw [hx2, map_one]

/-- Every elementary eight in a central product of two quaternion eights is
self-centralizing within that central product. -/
public theorem inf_centralizer_elementary_eight_of_quaternion_factors
    {G : Type*} [Group G] [Finite G] (B C U : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 8) (hUV : U ≤ B ⊔ C) :
    (B ⊔ C) ⊓ centralizer (U : Set G) = U := by
  classical
  have hBn : C ≤ normalizer (B : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro c hc b hb
    exact hcomm b hb c hc
  have hCn : B ≤ normalizer (C : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro b hb c hc
    exact (hcomm b hb c hc).symm
  have hVBn : B ⊔ C ≤ normalizer (B : Set G) := sup_le B.le_normalizer hBn
  have hVCn : B ⊔ C ≤ normalizer (C : Set G) := sup_le hCn C.le_normalizer
  have hBcard : Nat.card B = 8 := by
    obtain ⟨e⟩ := hB
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hCcard : Nat.card C = 8 := by
    obtain ⟨e⟩ := hC
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hVcard : Nat.card (B ⊔ C : Subgroup G) = 32 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes B C hBn
    rw [hBcard, hCcard, hinter] at hh
    omega
  have hUBI := inf_le_shared_center_of_elementary B C U hB hinter hcomm
  have hUCI : U ⊓ C ≤ B ⊓ C := by
    rw [inf_comm B C]
    exact inf_le_shared_center_of_elementary C B U hC
      (by simpa only [inf_comm] using hinter) (fun c hc b hb => (hcomm b hb c hc).symm)
  have hUBcard : Nat.card (U ⊓ B : Subgroup G) = 2 := by
    have hle : Nat.card (U ⊓ B : Subgroup G) ≤ 2 := by
      simpa only [hinter] using card_le_of_le hUBI
    have hsup : Nat.card (U ⊔ B : Subgroup G) ≤ 32 := by
      simpa only [hVcard] using card_le_of_le (sup_le hUV le_sup_left)
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes B U (hUV.trans hVBn)
    rw [hBcard, hU, inf_comm B U, sup_comm B U] at hh
    interval_cases hc : Nat.card (U ⊓ B : Subgroup G) <;> omega
  have hUCcard : Nat.card (U ⊓ C : Subgroup G) = 2 := by
    have hle : Nat.card (U ⊓ C : Subgroup G) ≤ 2 := by
      simpa only [hinter] using card_le_of_le hUCI
    have hsup : Nat.card (U ⊔ C : Subgroup G) ≤ 32 := by
      simpa only [hVcard] using card_le_of_le (sup_le hUV le_sup_right)
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes C U (hUV.trans hVCn)
    rw [hCcard, hU, inf_comm C U, sup_comm C U] at hh
    interval_cases hc : Nat.card (U ⊓ C : Subgroup G) <;> omega
  have hIU : B ⊓ C ≤ U := by
    have hh : U ⊓ B = B ⊓ C := eq_of_le_of_card_ge hUBI (by rw [hUBcard, hinter])
    exact hh.symm.le.trans inf_le_left
  have hUB : U ⊔ B = B ⊔ C := by
    apply eq_of_le_of_card_ge (sup_le hUV le_sup_left)
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes B U (hUV.trans hVBn)
    rw [hBcard, hU, inf_comm B U, hUBcard, sup_comm B U] at hh
    rw [hVcard]
    omega
  have hUC : U ⊔ C = B ⊔ C := by
    apply eq_of_le_of_card_ge (sup_le hUV le_sup_right)
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes C U (hUV.trans hVCn)
    rw [hCcard, hU, inf_comm C U, hUCcard, sup_comm C U] at hh
    rw [hVcard]
    omega
  have hUU : U ≤ centralizer (U : Set G) := le_centralizer_iff_isMulCommutative.mpr inferInstance
  apply le_antisymm ?_ (le_inf hUV hUU)
  intro x hx
  have hxprod : x ∈ (U : Set G) * (C : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right U C (hUV.trans hVCn), hUC]
    exact hx.1
  obtain ⟨u, hu, c, hc, huc⟩ := hxprod
  have hcfix : c ∈ centralizer (U : Set G) := by
    have hh := (centralizer (U : Set G)).mul_mem
      ((centralizer (U : Set G)).inv_mem (hUU hu)) hx.2
    rw [← huc] at hh
    simpa only [inv_mul_cancel_left] using hh
  have hcV : B ⊔ C ≤ centralizer ({c} : Set G) := by
    rw [← hUB]
    apply sup_le
    · intro v hv
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hcfix v hv)
    · intro b hb
      exact mem_centralizer_singleton_iff.mpr (hcomm b hb c hc)
  have hcz : (⟨c, hc⟩ : C) ∈ center C := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hcV (mem_sup_right y.property)))
  have hcenterC : B ⊓ C = (center C).map C.subtype := by
    rw [inf_comm]
    exact intersection_eq_factor_center C B hC (by simpa only [inf_comm] using hinter)
      (fun c hc b hb => (hcomm b hb c hc).symm)
  have hcI : c ∈ B ⊓ C := by
    rw [hcenterC]
    exact ⟨⟨c,hc⟩, hcz, rfl⟩
  rw [← huc]
  exact U.mul_mem hu (hIU hcI)

end Subgroup
