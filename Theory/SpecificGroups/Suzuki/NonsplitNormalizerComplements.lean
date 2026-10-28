module

public import Theory.SpecificGroups.Suzuki.MaximalNonsplitTori
public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# Complements in an index-four nonsplit normalizer

The cyclic normalizer action from `MaximalNonsplitTori` identifies an
index-four normalizer with a cyclic group of order four.  Schur--Zassenhaus
then supplies a complement to the (odd-order) nonsplit subgroup.  We choose
the orientation of a generator so that the right conjugation action is the
first Frobenius power.
-/

namespace BenderSuzuki.MatrixGroups

private theorem nonsplit_normalizer_action_data {m : ℕ} (hm : 0 < m)
    {U : Subgroup (SuzukiMatrixGroup m)} (hU : IsSuzukiMaximalNonsplit m U) :
    let _ := hU.isCyclic hm
    ∃ β : MulAut U, β ^ 4 = 1 ∧
      (∀ u : U, β u = u ^ (2 ^ (2 * m + 1))) ∧
      ∀ (g : SuzukiMatrixGroup m) (hg : g ∈ Subgroup.normalizer (U : Set _)),
        ∃ i : ℕ, i < 4 ∧ U.normalizerMonoidHom ⟨g, hg⟩ = β ^ i := by
  let _ := hU.isCyclic hm
  let _ := IsCyclic.commGroup (α := U)
  let q := 2 ^ (2 * m + 1)
  have hcop : Nat.Coprime (Nat.card U) q := by
    apply Nat.Coprime.of_dvd_left hU.card_dvd
    exact Nat.Coprime.of_dvd_right (dvd_pow_self q (by decide : 2 ≠ 0))
      (Nat.coprime_self_add_left.mpr (Nat.coprime_one_left (q ^ 2)))
  let β : MulAut U := { powCoprime hcop with map_mul' := fun a b => mul_pow a b q }
  have hβ (u : U) : β u = u ^ q := rfl
  have hβpow (i : ℕ) (u : U) : (β ^ i) u = u ^ (q ^ i) := by
    induction i generalizing u with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, MulAut.mul_apply, hβ, ih, ← pow_mul, pow_succ']
  have hβsq (u : U) : (β ^ 2) u = u⁻¹ := by
    rw [hβpow]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    exact orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_natCard u).trans hU.card_dvd)
  have hβfour : β ^ 4 = 1 := by
    apply MulEquiv.ext
    intro u
    change (β ^ (2 + 2)) u = u
    rw [pow_add, MulAut.mul_apply, hβsq, hβsq, inv_inv]
  refine ⟨β, hβfour, hβ, ?_⟩
  intro g hg
  obtain ⟨i, hi, hpow⟩ :=
    suzukiMatrixGroup_normalizer_eq_frobenius_pow_of_card_dvd_sq_add_one m hm U
      (hU.ne_bot hm) hU.card_dvd g⁻¹
      ((Subgroup.normalizer (U : Set (SuzukiMatrixGroup m))).inv_mem hg)
  refine ⟨i, hi, ?_⟩
  apply MulEquiv.ext
  intro u
  apply Subtype.ext
  have h := hpow (u : SuzukiMatrixGroup m) u.property
  rw [hβpow]
  change g * (u : SuzukiMatrixGroup m) * g⁻¹ =
    (u : SuzukiMatrixGroup m) ^ (q ^ i)
  simpa only [inv_inv] using h

private theorem odd_degree_coprime_four (m : ℕ) :
    Nat.Coprime ((2 ^ (2 * m + 1)) ^ 2 + 1) 4 := by
  have heven : Even ((2 : ℕ) ^ (2 * m + 1)) :=
    even_two.pow_of_ne_zero (by omega)
  have hodd : Odd ((2 ^ (2 * m + 1)) ^ 2 + 1) := by
    obtain ⟨k, hk⟩ := heven
    rw [hk]
    use 2 * k ^ 2
    simp [pow_two]
    ring
  exact (Nat.coprime_two_right.mpr hodd).pow_right 2

/-- An index-four maximal nonsplit normalizer has a cyclic complement of order
four, with the source's right-conjugation Frobenius orientation. -/
public theorem exists_suzuki_nonsplit_order_four_complement (m : ℕ) (hm : 0 < m)
    {U : Subgroup (SuzukiMatrixGroup m)} (hU : IsSuzukiMaximalNonsplit m U)
    (hindex : U.relIndex (Subgroup.normalizer (U : Set (SuzukiMatrixGroup m))) = 4) :
    ∃ t : SuzukiMatrixGroup m,
      orderOf t = 4 ∧
      t ∈ Subgroup.normalizer (U : Set (SuzukiMatrixGroup m)) ∧
      U ⊔ Subgroup.zpowers t = Subgroup.normalizer (U : Set (SuzukiMatrixGroup m)) ∧
      Disjoint U (Subgroup.zpowers t) ∧
      ∀ u ∈ U, t⁻¹ * u * t = u ^ (2 ^ (2 * m + 1)) := by
  let N : Subgroup (SuzukiMatrixGroup m) := Subgroup.normalizer (U : Set _)
  have hUN : U ≤ N := Subgroup.le_normalizer
  let H : Subgroup N := U.subgroupOf N
  let _ : H.Normal := Subgroup.normal_subgroupOf_of_le_normalizer (show N ≤ Subgroup.normalizer (U : Set _) by rfl)
  have hHcard : Nat.card H = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUN).toEquiv
  have hHindex : H.index = 4 := by
    change U.relIndex (Subgroup.normalizer (U : Set (SuzukiMatrixGroup m))) = 4
    exact hindex
  have hcop : Nat.Coprime (Nat.card H) H.index := by
    rw [hHcard, hHindex]
    exact Nat.Coprime.of_dvd_right (by decide : 4 ∣ 4)
      (odd_degree_coprime_four m |>.of_dvd_left hU.card_dvd)
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hKcard : Nat.card K = 4 := by
    have hmul := hK.card_mul_card
    have hNcard := H.card_mul_index
    rw [hHindex] at hNcard
    apply Nat.mul_left_cancel (n := Nat.card H)
    · exact Nat.card_pos
    · exact hmul.trans hNcard.symm
  let _ := hU.isCyclic hm
  obtain ⟨β, hβfour, hβeval, hβaction⟩ := nonsplit_normalizer_action_data hm hU
  let f : K →* MulAut U := U.normalizerMonoidHom.comp K.subtype
  have hf : Function.Injective f := by
    intro a b hab
    have hab' : f (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab]
      exact mul_inv_cancel _
    have hx : (K.subtype (a * b⁻¹) : N) ∈ H := by
      have hx' : K.subtype (a * b⁻¹) ∈ U.normalizerMonoidHom.ker := by
        rw [MonoidHom.mem_ker]
        exact hab'
      rw [Subgroup.normalizerMonoidHom_ker] at hx'
      change ((K.subtype (a * b⁻¹) : N) : SuzukiMatrixGroup m) ∈
        Subgroup.centralizer (U : Set (SuzukiMatrixGroup m)) at hx'
      rw [hU.centralizer_subgroup_eq hm] at hx'
      exact hx'
    have hz : a * b⁻¹ = 1 := by
      have hz' := Subgroup.disjoint_def.mp hK.disjoint hx (a * b⁻¹).property
      exact Subtype.ext hz'
    exact eq_of_mul_inv_eq_one hz
  have hf_range_le : f.range ≤ Subgroup.zpowers β := by
    rintro x ⟨a, rfl⟩
    obtain ⟨i, hi, hia⟩ := hβaction (K.subtype a) (K.subtype a).property
    have hia' : f a = β ^ i := by simpa [f] using hia
    rw [hia']
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers β) _
  let _ : IsCyclic f.range := Subgroup.isCyclic_of_le hf_range_le
  let _ : IsCyclic K := isCyclic_of_injective f.rangeRestrict (by
    intro a b hab
    apply hf
    exact congrArg Subtype.val hab)
  obtain ⟨k, hk⟩ := IsCyclic.exists_generator (α := K)
  have hkz : Subgroup.zpowers k = ⊤ := by
    apply top_unique
    intro x hx
    exact hk x
  have hkorder : orderOf k = 4 := by
    rw [← Nat.card_zpowers k, hkz]
    norm_num [hKcard]
  have hkambient : orderOf (k : SuzukiMatrixGroup m) = 4 := by
    simpa only [Subgroup.orderOf_coe] using hkorder
  have hkN : (k : SuzukiMatrixGroup m) ∈ N := (k : N).property
  have hk_invN : ((k : SuzukiMatrixGroup m)⁻¹) ∈ N := N.inv_mem hkN
  obtain ⟨i, hi, hki⟩ := hβaction (k : SuzukiMatrixGroup m)⁻¹ hk_invN
  have hfiorder : orderOf (f (k⁻¹)) = 4 := by
    rw [orderOf_injective f hf]
    simp [hkorder]
  have hi_cases : i = 1 ∨ i = 3 := by
    interval_cases i
    · have hzero : f (k⁻¹) = 1 := by
        change U.normalizerMonoidHom (K.subtype (k⁻¹)) = 1
        change U.normalizerMonoidHom ⟨(k : SuzukiMatrixGroup m)⁻¹, hk_invN⟩ = 1
        exact hki
      rw [hzero, orderOf_one] at hfiorder
      omega
    · exact Or.inl rfl
    · have hp : (f (k⁻¹)) ^ 2 = 1 := by
        rw [show f (k⁻¹) = β ^ 2 from hki, ← pow_mul,
          show 2 * 2 = 4 by norm_num, hβfour]
      have hd := orderOf_dvd_of_pow_eq_one hp
      rw [hfiorder] at hd
      omega
    · exact Or.inr rfl
  have hmapH : Subgroup.map N.subtype H = U :=
    Subgroup.map_subgroupOf_eq_of_le hUN
  have hmapK : Subgroup.map N.subtype K =
      Subgroup.zpowers (k : SuzukiMatrixGroup m) := by
    let φ := N.subtype.comp K.subtype
    have hφ : Subgroup.map φ (Subgroup.zpowers k) =
        Subgroup.zpowers (k : SuzukiMatrixGroup m) := by
      change Subgroup.map φ (Subgroup.zpowers k) = Subgroup.zpowers (φ k)
      exact MonoidHom.map_zpowers φ k
    apply le_antisymm
    · apply Subgroup.map_le_iff_le_comap.mpr
      intro a ha
      rw [← hφ]
      let aK : K := ⟨a, ha⟩
      exact Subgroup.mem_map.mpr ⟨aK, hk aK, rfl⟩
    · apply Subgroup.zpowers_le.mpr
      exact Subgroup.mem_map.mpr ⟨k, k.property, rfl⟩
  rcases hi_cases with rfl | hi3
  · refine ⟨(k : SuzukiMatrixGroup m), hkambient, hkN, ?_, ?_, ?_⟩
    · have hmapTop : Subgroup.map N.subtype (⊤ : Subgroup N) = N := by
        rw [← MonoidHom.range_eq_map, N.range_subtype]
      calc
        U ⊔ Subgroup.zpowers (k : SuzukiMatrixGroup m) =
            Subgroup.map N.subtype H ⊔ Subgroup.map N.subtype K := by rw [hmapH, hmapK]
        _ = Subgroup.map N.subtype (H ⊔ K) := (Subgroup.map_sup H K N.subtype).symm
        _ = Subgroup.map N.subtype (⊤ : Subgroup N) := by rw [hK.sup_eq_top]
        _ = N := hmapTop
    · have hd := Subgroup.disjoint_map N.subtype_injective hK.disjoint
      rw [hmapH, hmapK] at hd
      exact hd
    · intro u hu
      have h := congrArg (fun e : MulAut U => e ⟨u, hu⟩) hki
      simpa [hβeval] using congrArg Subtype.val h
  · have hk3 := hki
    have hk3' : f (k⁻¹) = β ^ 3 := by
      change U.normalizerMonoidHom ⟨(k : SuzukiMatrixGroup m)⁻¹, hk_invN⟩ = β ^ 3
      simpa [hi3] using hk3
    have hfk : f k = β := by
      have hh := congrArg Inv.inv hk3'
      have hb : (β ^ 3)⁻¹ = β := by
        have hh : β = (β ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right (by
          rw [← pow_succ, hβfour])
        exact hh.symm
      simpa [map_inv, hb] using hh
    refine ⟨(k : SuzukiMatrixGroup m)⁻¹, by simpa using hkambient, hk_invN, ?_, ?_, ?_⟩
    · have hmapTop : Subgroup.map N.subtype (⊤ : Subgroup N) = N := by
        rw [← MonoidHom.range_eq_map, N.range_subtype]
      calc
        U ⊔ Subgroup.zpowers ((k : SuzukiMatrixGroup m)⁻¹) =
            Subgroup.map N.subtype H ⊔ Subgroup.map N.subtype K := by
              rw [hmapH, hmapK, Subgroup.zpowers_inv]
        _ = Subgroup.map N.subtype (H ⊔ K) := (Subgroup.map_sup H K N.subtype).symm
        _ = Subgroup.map N.subtype (⊤ : Subgroup N) := by rw [hK.sup_eq_top]
        _ = N := hmapTop
    · have hd := Subgroup.disjoint_map N.subtype_injective hK.disjoint
      rw [hmapH, hmapK] at hd
      simpa [Subgroup.zpowers_inv] using hd
    · intro u hu
      have h := congrArg (fun e : MulAut U => e ⟨u, hu⟩) hfk
      change (MulDistribMulAction.toMulAut N U ⟨(k : SuzukiMatrixGroup m), hkN⟩) ⟨u, hu⟩ =
        β ⟨u, hu⟩ at h
      rw [MulDistribMulAction.toMulAut_apply] at h
      change ((⟨(k : SuzukiMatrixGroup m), hkN⟩ : N) • (⟨u, hu⟩ : U)) =
        β ⟨u, hu⟩ at h
      have hval := congrArg Subtype.val h
      change ((k : SuzukiMatrixGroup m) * (u : SuzukiMatrixGroup m) * (k : SuzukiMatrixGroup m)⁻¹) =
        (β ⟨u, hu⟩ : SuzukiMatrixGroup m) at hval
      simpa [hβeval] using hval

/- The method-style form used by downstream Suzuki arguments. -/
public theorem IsSuzukiMaximalNonsplit.exists_order_four_complement
    {m : ℕ} (hm : 0 < m) {U : Subgroup (SuzukiMatrixGroup m)}
    (hU : IsSuzukiMaximalNonsplit m U)
    (hindex : U.relIndex (Subgroup.normalizer (U : Set (SuzukiMatrixGroup m))) = 4) :
    ∃ t : SuzukiMatrixGroup m,
      orderOf t = 4 ∧
      t ∈ Subgroup.normalizer (U : Set (SuzukiMatrixGroup m)) ∧
      U ⊔ Subgroup.zpowers t = Subgroup.normalizer (U : Set (SuzukiMatrixGroup m)) ∧
      Disjoint U (Subgroup.zpowers t) ∧
      ∀ u ∈ U, t⁻¹ * u * t = u ^ (2 ^ (2 * m + 1)) :=
  exists_suzuki_nonsplit_order_four_complement m hm hU hindex

end BenderSuzuki.MatrixGroups
