module
public import ABG.ChapterII.Section1.WreathedExceptionalBase
public import ABG.ChapterII.Section1.WreathedInvolutions
public import Theory.GroupTheory.CharacteristicIndexTwoAut
public import Theory.GroupTheory.SpecificGroups.AbelianTwoFactorAut

/-!
# Automorphisms of the modular small central extension

The canonical subgroup `modularOvergroup` in the chosen wreathed presentation
has a two-group of automorphisms. This rules out the second small central
extension in ABG Chapter II §1 Lemma 3(i), article p.10, when the relevant
subgroup has a nonidentity automorphism of odd order.

The subgroup `exceptionalBase = center S ⊔ ⟨x₂⟩` is normal and has type
`(2^n, 2)`, by `WreathedExceptionalBase`. Collecting powers of `sz`, whose
square is `u`, gives two cosets of this base in `modularOvergroup`. Base
elements have `2^n`-th power one, whereas every element in the other coset
has `2^n`-th power `x`, the central involution. The height bound `n ≥ 2`
ensures this also holds for the coset represented by `x₂*sz`. Thus the
base inside the modular subgroup is defined by the power-one condition
and is characteristic. Its automorphism group is a two-group by the unequal
cyclic-factor theorem, so the characteristic-index-two automorphism theorem
proves the result. All groups are actual subgroups of the chosen presentation.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

private theorem u_pow : P.u ^ (2 ^ n) = 1 := by rw [← P.orderOf_u, pow_orderOf_eq_one]

include P in
private theorem half_double : 2 ^ (n-1) * 2 = 2 ^ n := by
  rw [← pow_succ]
  congr 1
  have := P.height
  omega

private theorem sz_pow : (P.s * P.z) ^ (2 ^ n) = P.x := by
  rw [← P.half_double, Nat.mul_comm, pow_mul, P.sz_sq]
  rfl

private theorem x_half : P.x ^ (2 ^ (n-1)) = 1 := by
  have he : 2 ^ (n-1) = 2 * 2 ^ (n-2) := by
    rw [Nat.mul_comm, ← pow_succ]
    congr 1
    have := P.height
    omega
  rw [he, pow_mul, ← P.x_orderOf, pow_orderOf_eq_one, one_pow]

private theorem x₂_sz_sq : (P.x₂ * (P.s * P.z)) ^ 2 = P.x * P.u := by
  have hswap : (P.s * P.z) * P.x₂ = P.x₃ * (P.s * P.z) := by
    rw [mul_assoc, x₂, P.z_mul_s_pow, ← mul_assoc,
      (show Commute P.s P.t from P.commute).pow_right (2^(n-1)) |>.eq]
    simp only [x₃, mul_assoc]
  calc
    _ = P.x₂ * ((P.s * P.z) * P.x₂) * (P.s * P.z) := by simp only [pow_two]; group
    _ = P.x₂ * (P.x₃ * (P.s * P.z)) * (P.s * P.z) := by rw [hswap]
    _ = (P.x₂ * P.x₃) * (P.s * P.z) ^ 2 := by simp only [pow_two]; group
    _ = P.x * P.u := by rw [P.x_eq_x₂_mul_x₃, P.sz_sq]

private theorem x₂_sz_pow : (P.x₂ * (P.s * P.z)) ^ (2 ^ n) = P.x := by
  have hc : Commute P.x P.u := ((Subgroup.mem_center_iff.mp P.x_mem_center) P.u).symm
  rw [← P.half_double, Nat.mul_comm, pow_mul, P.x₂_sz_sq, hc.mul_pow,
    P.x_half, one_mul]
  rfl

private theorem base_pow
    {g : S} (hg : g ∈ P.exceptionalBase) : g ^ (2 ^ n) = 1 := by
  obtain ⟨i,e,rfl⟩ := P.exists_exceptionalBase_form hg
  have hc : Commute P.u P.x₂ := ((Subgroup.mem_center_iff.mp P.u_mem_center) P.x₂).symm
  rw [(hc.pow_pow _ _).mul_pow]
  have hu : (P.u ^ i.val) ^ (2^n) = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, P.u_pow, one_pow]
  have hx : (P.x₂ ^ e.val) ^ (2^n) = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, ← P.half_double, Nat.mul_comm,
      pow_mul, P.x₂_sq, one_pow, one_pow]
  rw [hu, hx, one_mul]

private theorem outer_base_pow
    {g : S} (hg : g ∈ P.exceptionalBase) : (g * (P.s * P.z)) ^ (2 ^ n) = P.x := by
  obtain ⟨i,e,rfl⟩ := P.exists_exceptionalBase_form hg
  have he : e.val = 0 ∨ e.val = 1 := by omega
  have hu : (P.u ^ i.val) ^ (2^n) = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, P.u_pow, one_pow]
  rcases he with he | he
  · simp only [he, pow_zero, mul_one]
    have hc : Commute (P.u ^ i.val) (P.s * P.z) :=
      Commute.pow_left ((Subgroup.mem_center_iff.mp P.u_mem_center) (P.s * P.z)).symm _
    rw [hc.mul_pow, hu, one_mul, P.sz_pow]
  · simp only [he, pow_one, mul_assoc]
    have hc : Commute (P.u ^ i.val) (P.x₂ * (P.s * P.z)) :=
      Commute.pow_left ((Subgroup.mem_center_iff.mp P.u_mem_center) (P.x₂ * (P.s * P.z))).symm _
    rw [hc.mul_pow, hu, one_mul, P.x₂_sz_pow]

private theorem sz_zpow_form (k : ℤ) :
    (P.s * P.z) ^ k = P.u ^ (k / 2) * (P.s * P.z) ^ (k % 2) := by
  calc
    _ = (P.s * P.z) ^ (2 * (k / 2) + k % 2) := by congr 1; omega
    _ = _ := by rw [zpow_add, zpow_mul]; norm_num only [zpow_ofNat, P.sz_sq]

private theorem modular_form
    {g : S} (hg : g ∈ P.modularOvergroup) :
    ∃ b ∈ P.exceptionalBase, g = b ∨ g = b * (P.s * P.z) := by
  let := P.exceptionalBase_normal
  obtain ⟨b,hb,a,ha,rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
  obtain ⟨k,rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hu := P.u_mem_exceptionalBase
  refine ⟨b * P.u ^ (k/2), P.exceptionalBase.mul_mem hb (P.exceptionalBase.zpow_mem hu _), ?_⟩
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rw [P.sz_zpow_form]
  rcases hk with hk | hk
  · left; simp only [hk, zpow_zero, mul_one]
  · right; simp only [hk, zpow_one, mul_assoc]

private theorem sz_not_base : P.s * P.z ∉ P.exceptionalBase := by
  intro hh
  apply P.z_not_mem_U
  have hs : P.s ∈ P.U := Subgroup.subset_closure (by simp)
  simpa only [inv_mul_cancel_left] using P.U.mul_mem (P.U.inv_mem hs) (P.exceptionalBase_le_U hh)

private theorem modular_index :
    P.exceptionalBase.relIndex P.modularOvergroup = 2 := by
  rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
  refine ⟨P.s * P.z, (show Subgroup.zpowers (P.s * P.z) ≤ P.modularOvergroup from le_sup_right)
    (Subgroup.mem_zpowers _), P.sz_not_base, ?_⟩
  intro g hg
  obtain ⟨b,hb,rfl | rfl⟩ := P.modular_form hg
  · exact Or.inr hb
  · left
    have hu := P.u_mem_exceptionalBase
    simpa only [mul_assoc, ← pow_two, P.sz_sq] using P.exceptionalBase.mul_mem hb hu

private theorem modular_pow_iff
    {g : S} (hg : g ∈ P.modularOvergroup) :
    g ^ (2 ^ n) = 1 ↔ g ∈ P.exceptionalBase := by
  constructor
  · intro hpow
    obtain ⟨b,hb,rfl | rfl⟩ := P.modular_form hg
    · exact hb
    · have he := P.outer_base_pow hb
      rw [hpow] at he
      have hh := P.x_orderOf
      rw [← he, orderOf_one] at hh
      norm_num at hh
  · exact P.base_pow

private theorem modular_base_characteristic :
    (P.exceptionalBase.subgroupOf P.modularOvergroup).Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  intro f g hg
  have hp : g ^ (2^n) = 1 := Subtype.ext (P.base_pow hg)
  have hf : (f g) ^ (2^n) = 1 := by rw [← map_pow, hp, map_one]
  exact (P.modular_pow_iff (f g).property).mp (congrArg Subtype.val hf)

public theorem modular_aut_isPGroup :
    IsPGroup 2 (MulAut P.modularOvergroup) := by
  let : Finite S := Nat.finite_of_card_ne_zero (by rw [P.card]; positivity)
  let C := P.exceptionalBase.subgroupOf P.modularOvergroup
  let : C.Characteristic := P.modular_base_characteristic
  have hG : IsPGroup 2 S := IsPGroup.of_card P.card
  have he : C ≃* P.exceptionalBase := Subgroup.subgroupOfEquivOfLe
    (show P.exceptionalBase ≤ P.modularOvergroup from le_sup_left)
  have hAB := abelian_two_factor_aut_isPGroup_of_equiv P.height P.exceptionalBaseEquiv
  have hAC : IsPGroup 2 (MulAut C) := hAB.of_equiv (MulAut.congr he).symm
  exact C.isPGroup_mulAut_of_characteristic_index_two P.modular_index
    ((hG.to_subgroup P.modularOvergroup).to_subgroup C) hAC
end ABG.Wreathed.Presentation
