module

public import Theory.GroupTheory.PGroup.SymplecticType
public import Theory.GroupTheory.SemidihedralCenter
public import Theory.GroupTheory.SpecificGroups.QuaternionCentralSquareEmbedding
public import Mathlib.Tactic.LinearCombination

/-!
# Large rotations in binary Hall factors

A noncyclic binary Hall factor of order at least sixteen has a rotation `r`
whose order is divisible by eight. Every square and every central element lies
in `⟨r²⟩`, the centralizer of `r²` lies in `⟨r⟩`, and the halfway power of `r`
is central.

For the dihedral and quaternion models these assertions follow from their two
normal forms. An outside element commuting with `r²` would force the rotation
order to divide four. In the semidihedral presentation the same obstruction
follows from the half-order divisibility calculation; its center has already
been computed in `SemidihedralCenter`. The two-group hypothesis forces the
arbitrary dihedral rotation parameter to be a power of two. The calculations
are transported through the equivalences in `IsBinaryHallFactor`.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, Case 1, p. 392
(`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`).
The model laws are Mathlib's dihedral and quaternion laws and the explicit
semidihedral presentation used in `SymplecticType`.
-/

open Subgroup

private def LargeRotation {G : Type*} [Group G] (r : G) : Prop :=
  8 ∣ orderOf r ∧
  (∀ d : G, d ^ 2 ∈ zpowers (r ^ 2)) ∧
  center G ≤ zpowers (r ^ 2) ∧
  centralizer ({r ^ 2} : Set G) ≤ zpowers r ∧
  r ^ (orderOf r / 2) ∈ center G

private theorem pow_mem_square {G : Type*} [Group G] (r : G) {i : ℕ}
    (hi : 2 ∣ i) : r ^ i ∈ zpowers (r ^ 2) := by
  obtain ⟨k, rfl⟩ := hi
  rw [pow_mul]
  exact pow_mem (mem_zpowers _) _

private theorem involution_power_mem_square {G : Type*} [Group G] (r : G)
    (hfour : 4 ∣ orderOf r) (i : ℕ) (hi : (r ^ i) ^ 2 = 1) :
    r ^ i ∈ zpowers (r ^ 2) := by
  have hd : 4 ∣ i * 2 := hfour.trans (orderOf_dvd_of_pow_eq_one (by
    simpa only [pow_mul] using hi))
  apply pow_mem_square
  omega

private theorem largeRotation_map {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {r : G} (h : LargeRotation r) : LargeRotation (e r) := by
  rcases h with ⟨hord, hsq, hZ, hC, hhalf⟩
  have hmem {x y : G} (h : x ∈ zpowers y) : e x ∈ zpowers (e y) := by
    obtain ⟨k, rfl⟩ := h
    exact ⟨k, by simp⟩
  refine ⟨by simpa using hord, ?_, ?_, ?_, ?_⟩
  · intro d
    obtain ⟨d, rfl⟩ := e.surjective d
    simpa only [map_pow] using hmem (hsq d)
  · intro z hz
    obtain ⟨z, rfl⟩ := e.surjective z
    have hz' : z ∈ center G := by
      apply mem_center_iff.mpr
      intro x
      apply e.injective
      simpa only [map_mul] using mem_center_iff.mp hz (e x)
    simpa only [map_pow] using hmem (hZ hz')
  · intro d hd
    obtain ⟨d, rfl⟩ := e.surjective d
    apply hmem
    apply hC
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    apply e.injective
    simpa only [map_mul, map_pow] using hd ((e r) ^ 2) (by simp)
  · rw [e.orderOf_eq, ← map_pow]
    apply mem_center_iff.mpr
    intro d
    obtain ⟨d, rfl⟩ := e.surjective d
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hhalf d)

private theorem dihedral_large_rotation {m : ℕ} (hm : 8 ≤ m) (hdiv : 8 ∣ m) :
    LargeRotation (DihedralGroup.r 1 : DihedralGroup m) := by
  let : NeZero m := ⟨by omega⟩
  have hr (i : ZMod m) : DihedralGroup.r i ∈ zpowers (DihedralGroup.r 1 : DihedralGroup m) := by
    have h := pow_mem (mem_zpowers (DihedralGroup.r 1 : DihedralGroup m)) i.val
    simpa only [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val] using h
  have hC : centralizer ({(DihedralGroup.r 1 : DihedralGroup m) ^ 2} : Set _) ≤
      zpowers (DihedralGroup.r 1) := by
    intro x hx
    cases x with
    | r i => exact hr i
    | sr i =>
      have hi : i - 2 = i + 2 := DihedralGroup.sr.inj (by
        simpa only [DihedralGroup.r_one_pow, DihedralGroup.r_mul_sr,
          DihedralGroup.sr_mul_r, Nat.cast_ofNat] using hx _ (Set.mem_singleton _))
      have hfour : (4 : ZMod m) = 0 := by linear_combination -hi
      have hv := congrArg ZMod.val hfour
      have hval : ZMod.val (4 : ZMod m) = 4 := ZMod.val_natCast_of_lt (by omega : 4 < m)
      rw [hval, ZMod.val_zero] at hv
      omega
  refine ⟨by simpa only [DihedralGroup.orderOf_r_one] using hdiv, ?_, ?_, hC, ?_⟩
  · intro d
    cases d with
    | r i =>
      have he : DihedralGroup.r i = (DihedralGroup.r 1 : DihedralGroup m) ^ i.val := by
        simp only [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
      rw [he, pow_right_comm]
      exact pow_mem (mem_zpowers _) _
    | sr i => simp only [pow_two, DihedralGroup.sr_mul_self, one_mem]
  · intro x hx
    cases x with
    | r i =>
      have hi : i = -i := by
        simpa using mem_center_iff.mp hx (DihedralGroup.sr 0)
      have hs : (DihedralGroup.r i : DihedralGroup m) ^ 2 = 1 := by
        simp only [pow_two, DihedralGroup.r_mul_r, DihedralGroup.one_def]
        congr 1
        linear_combination hi
      have he : DihedralGroup.r i = (DihedralGroup.r 1 : DihedralGroup m) ^ i.val := by
        simp only [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
      rw [he] at hs ⊢
      exact involution_power_mem_square _ (by
        rw [DihedralGroup.orderOf_r_one]; exact (by decide : 4 ∣ 8).trans hdiv) _ hs
    | sr i =>
      have hi : i - 1 = i + 1 := DihedralGroup.sr.inj (mem_center_iff.mp hx (DihedralGroup.r 1))
      have htwo : (2 : ZMod m) = 0 := by linear_combination -hi
      have hv := congrArg ZMod.val htwo
      have hval : ZMod.val (2 : ZMod m) = 2 := ZMod.val_natCast_of_lt (by omega : 2 < m)
      rw [hval, ZMod.val_zero] at hv
      omega
  · rw [DihedralGroup.orderOf_r_one, DihedralGroup.r_one_pow]
    have heven : 2 ∣ m := (by decide : 2 ∣ 8).trans hdiv
    have hhalf : ((m / 2 : ℕ) : ZMod m) + ((m / 2 : ℕ) : ZMod m) = 0 := by
      have he : m / 2 + m / 2 = m := by omega
      exact_mod_cast (show ((m / 2 + m / 2 : ℕ) : ZMod m) = 0 by rw [he]; simp)
    apply mem_center_iff.mpr
    intro x
    cases x with
    | r i => simp [add_comm]
    | sr i =>
      simp only [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr]
      congr 1
      linear_combination hhalf

private theorem quaternion_large_rotation {m : ℕ} (hm : 4 ≤ m) (hdiv : 4 ∣ m) :
    LargeRotation (QuaternionGroup.a 1 : QuaternionGroup m) := by
  let : NeZero m := ⟨by omega⟩
  have hr (i : ZMod (2 * m)) : QuaternionGroup.a i ∈ zpowers (QuaternionGroup.a 1 : QuaternionGroup m) := by
    have h := pow_mem (mem_zpowers (QuaternionGroup.a 1 : QuaternionGroup m)) i.val
    simpa only [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val] using h
  have hhalf : QuaternionGroup.a (m : ZMod (2 * m)) ∈
      zpowers ((QuaternionGroup.a 1 : QuaternionGroup m) ^ 2) := by
    rw [← QuaternionGroup.a_one_pow]
    exact pow_mem_square _ ((by decide : 2 ∣ 4).trans hdiv)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [QuaternionGroup.orderOf_a_one]
    exact Nat.mul_dvd_mul_left 2 hdiv
  · intro d
    cases d with
    | a i =>
      have he : QuaternionGroup.a i = (QuaternionGroup.a 1 : QuaternionGroup m) ^ i.val := by
        simp only [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
      rw [he, pow_right_comm]
      exact pow_mem (mem_zpowers _) _
    | xa i => rw [QuaternionGroup.xa_sq]; exact hhalf
  · intro x hx
    rcases QuaternionGroup.eq_one_or_eq_a_of_sq_eq_one (by omega) x
      (QuaternionGroup.sq_eq_one_of_mem_center (by omega) x hx) with rfl | rfl
    · exact one_mem _
    · exact hhalf
  · intro x hx
    cases x with
    | a i => exact hr i
    | xa i =>
      have hi : i - 2 = i + 2 := QuaternionGroup.xa.inj (by
        simpa only [QuaternionGroup.a_one_pow, QuaternionGroup.a_mul_xa,
          QuaternionGroup.xa_mul_a, Nat.cast_ofNat] using hx _ (Set.mem_singleton _))
      have hfour : (4 : ZMod (2 * m)) = 0 := by linear_combination -hi
      have hv := congrArg ZMod.val hfour
      have hval : ZMod.val (4 : ZMod (2 * m)) = 4 := ZMod.val_natCast_of_lt (by omega : 4 < 2 * m)
      rw [hval, ZMod.val_zero] at hv
      omega
  · rw [QuaternionGroup.orderOf_a_one, Nat.mul_div_cancel_left _ (by decide : 0 < 2),
      QuaternionGroup.a_one_pow]
    have hhalf : (m : ZMod (2 * m)) + m = 0 := by
      have h : ((2 * m : ℕ) : ZMod (2 * m)) = 0 := by simp
      push_cast at h
      linear_combination h
    apply mem_center_iff.mpr
    intro x
    cases x with
    | a i => simp [add_comm]
    | xa i =>
      simp only [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa]
      congr 1
      linear_combination hhalf

private theorem semidihedral_large_rotation {G : Type*} [Group G] {n : ℕ}
    (hn : 4 ≤ n) (a b : G) (ha : orderOf a = 2 ^ (n - 1)) (hb : orderOf b = 2)
    (hconj : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : closure ({a, b} : Set G) = ⊤) : LargeRotation a := by
  have hp : 0 < 2 ^ (n - 2) := by positivity
  have hlow : 4 ≤ 2 ^ (n - 2) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ n - 2)
  have htwo : 2 ∣ 2 ^ (n - 2) := Nat.pow_dvd_pow 2 (by omega : 1 ≤ n - 2)
  have hb2 : b ^ 2 = 1 := hb ▸ pow_orderOf_eq_one b
  have hZ := Semidihedral.center_eq hn a b ha hb hconj hgen
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [ha]
    exact Nat.pow_dvd_pow 2 (by omega : 3 ≤ n - 1)
  · intro d
    obtain ⟨i, -, rfl | rfl⟩ := Semidihedral.normal_form a b _ _ (by positivity) ha hb2 hconj hgen d
    · rw [pow_right_comm]
      exact pow_mem (mem_zpowers _) _
    · have hsq : (a ^ i * b) ^ 2 = a ^ (2 ^ (n - 2) * i) := by
        calc
          _ = a ^ i * (b * a ^ i) * b := by simp only [pow_two]; group
          _ = a ^ i * (a ^ ((2 ^ (n - 2) - 1) * i) * b) * b := by
            rw [Semidihedral.move_pow a b _ hconj i]
          _ = a ^ (i + (2 ^ (n - 2) - 1) * i) := by
            rw [mul_assoc, mul_assoc, ← pow_two b, hb2, mul_one, ← pow_add]
          _ = _ := by
            congr 1
            have he : 1 + (2 ^ (n - 2) - 1) = 2 ^ (n - 2) := by omega
            simpa only [add_mul, one_mul] using congrArg (· * i) he
      rw [hsq]
      exact pow_mem_square _ (htwo.mul_right i)
  · rw [hZ]
    exact zpowers_le.mpr (pow_mem_square a htwo)
  · intro d hd
    obtain ⟨i, -, rfl | rfl⟩ := Semidihedral.normal_form a b _ _ (by positivity) ha hb2 hconj hgen d
    · exact pow_mem (mem_zpowers _) _
    · have hc : b * a ^ 2 = a ^ 2 * b := by
        apply mul_left_cancel (a := a ^ i)
        calc
          a ^ i * (b * a ^ 2) = (a ^ i * b) * a ^ 2 := (mul_assoc _ _ _).symm
          _ = a ^ 2 * (a ^ i * b) := (hd _ (Set.mem_singleton _)).symm
          _ = a ^ i * (a ^ 2 * b) := by
            rw [← mul_assoc, (Commute.pow_pow_self a 2 i).eq, mul_assoc]
      have heq : a ^ ((2 ^ (n - 2) - 1) * 2) = a ^ 2 := by
        apply mul_right_cancel (b := b)
        rw [← Semidihedral.move_pow a b _ hconj 2]
        exact hc
      have hdvd : 2 ^ (n - 1) ∣ (2 ^ (n - 2) - 2) * 2 := by
        have h := (pow_eq_pow_iff_modEq.mp heq).symm.dvd'
        rw [ha] at h
        convert h using 1
        omega
      have hsmall := Nat.le_of_dvd (by decide : 0 < 2) (Semidihedral.half_order_dvd hn hdvd)
      omega
  · rw [ha, show n - 1 = (n - 2) + 1 by omega, pow_succ,
      Nat.mul_div_cancel _ (by decide : 0 < 2), hZ]
    exact mem_zpowers _

/-- A noncyclic binary Hall factor of order at least sixteen admits a rotation
of order divisible by eight, containing all squares and the center in its square
subgroup, with no outside element centralizing its square and with central
half-order power. -/
public theorem IsBinaryHallFactor.exists_large_rotation {D : Type*} [Group D] [Finite D]
    (hP : IsPGroup 2 D) (hD : IsBinaryHallFactor D) (hnc : ¬ IsCyclic D)
    (hlarge : 16 ≤ Nat.card D) :
    ∃ r : D, 8 ∣ orderOf r ∧
      (∀ d : D, d ^ 2 ∈ Subgroup.zpowers (r ^ 2)) ∧
      Subgroup.center D ≤ Subgroup.zpowers (r ^ 2) ∧
      Subgroup.centralizer ({r ^ 2} : Set D) ≤ Subgroup.zpowers r ∧
      r ^ (orderOf r / 2) ∈ Subgroup.center D := by
  change ∃ r, LargeRotation r
  rcases hD with hcyc | ⟨n, hn, ⟨e⟩⟩ | ⟨m, ⟨e⟩⟩ | ⟨n, hn, _, a, b, ha, hb, hc, hg⟩
  · exact (hnc hcyc).elim
  · have hcard : Nat.card D = 4 * 2 ^ (n - 2) := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have hfour : 4 ≤ 2 ^ (n - 2) := by omega
    have hn4 : 2 ≤ n - 2 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hfour
    exact ⟨e.symm (QuaternionGroup.a 1), largeRotation_map e.symm
      (quaternion_large_rotation hfour (Nat.pow_dvd_pow 2 hn4))⟩
  · have hcard : Nat.card D = 2 * m := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have hm : 8 ≤ m := by omega
    obtain ⟨k, hk⟩ := (hP.of_surjective e.toMonoidHom e.surjective).exists_orderOf_eq_pow
      (DihedralGroup.r 1)
    rw [DihedralGroup.orderOf_r_one] at hk
    have hthree : 3 ≤ k := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hk ▸ hm)
    have hdiv : 8 ∣ m := hk ▸ Nat.pow_dvd_pow 2 hthree
    exact ⟨e.symm (DihedralGroup.r 1), largeRotation_map e.symm (dihedral_large_rotation hm hdiv)⟩
  · exact ⟨a, semidihedral_large_rotation hn a b ha hb hc hg⟩
