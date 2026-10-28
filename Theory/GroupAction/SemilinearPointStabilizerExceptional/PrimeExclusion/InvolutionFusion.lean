module

public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeExclusion.Preparation
public import Theory.GroupTheory.Involution.OddRotation
public import Theory.GroupTheory.InvolutionOddProduct
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Involution fusion in the prime-degree semilinear action

The first assertion of GLS, Volume 4, Chapter 1, Lemma 3.10.  The proof uses
the checked Baer--Suzuki odd-rotation extraction and the literal KΓ action.
-/

public section

namespace MulAction.SemilinearPointStabilizer.PrimeExclusion

open BenderSuzuki PFAppendixIII
open MulAction.SemilinearPointStabilizer

variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F]
  [MulAction X F] [FaithfulSMul X F]

omit [Finite X] in
private theorem card_group_eq (c : Coordinates X F) (htwo : IsMultiplyPretransitive X F 2)
    {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hΓ : Nat.card (twoPoint (X := X) (F := F)) = n) :
    Nat.card X = 2 ^ n * ((2 ^ n - 1) * n) := by
  let _ : IsMultiplyPretransitive X F 2 := htwo
  let _ : IsPretransitive X F := isPretransitive_of_is_two_pretransitive
  rw [c.card_group, hF, hΓ]
  ac_rfl

omit [Finite X] in
private theorem prime_dvd_mersenne_or_degree
    (c : Coordinates X F) (htwo : IsMultiplyPretransitive X F 2)
    {n q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hF : Nat.card F = 2 ^ n)
    (hΓ : Nat.card (twoPoint (X := X) (F := F)) = n)
    (hr : q ∣ Nat.card X) : q ∣ 2 ^ n - 1 ∨ q ∣ n := by
  have hcard := hr
  rw [card_group_eq c htwo hF hΓ] at hcard
  rcases (hq.dvd_mul.mp hcard) with hpow | hrest
  · have hq2' : q ∣ 2 := hq.dvd_of_dvd_pow (by simpa using hpow)
    rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hq2' with h | h
    · exact (hq.ne_one h).elim
    · exact (hq2 h).elim
  exact hq.dvd_mul.mp hrest

omit [Finite X] in
private theorem point_stabilizer_odd (c : Coordinates X F) (htwo : IsMultiplyPretransitive X F 2)
    {n : ℕ} (hn : Odd n) (hF : Nat.card F = 2 ^ n)
    (hΓ : Nat.card (twoPoint (X := X) (F := F)) = n) (a : F) :
    Odd (Nat.card (stabilizer X a)) := by
  let _ : IsMultiplyPretransitive X F 2 := htwo
  let _ : IsPretransitive X F := isPretransitive_of_is_two_pretransitive
  have hc := (stabilizer X a).card_mul_index
  rw [index_stabilizer_of_transitive, hF, card_group_eq c htwo hF hΓ] at hc
  have hcard : Nat.card (stabilizer X a) = (2 ^ n - 1) * n := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 ^ n by positivity)
    simpa [Nat.mul_comm] using hc
  rw [hcard]
  have hm : Odd (2 ^ n - 1) := by
    have he : Even (2 ^ n) := even_two.pow_of_ne_zero (by obtain ⟨k, hk⟩ := hn; omega)
    exact (Nat.odd_sub (Nat.one_le_pow n 2 (by decide))).mpr (by simpa using he)
  exact hm.mul hn

omit [Finite X] in
private theorem no_involution_fixed_point
    (c : Coordinates X F) (htwo : IsMultiplyPretransitive X F 2)
    {n : ℕ} (hn : Odd n) (hF : Nat.card F = 2 ^ n)
    (hΓ : Nat.card (twoPoint (X := X) (F := F)) = n)
    (t : X) (ht : orderOf t = 2) : ∀ a : F, t • a ≠ a := by
  let _ : IsMultiplyPretransitive X F 2 := htwo
  let _ : IsPretransitive X F := isPretransitive_of_is_two_pretransitive
  intro a ha
  let u : stabilizer X a := ⟨t, ha⟩
  have hu : orderOf u = 2 :=
    (orderOf_injective (stabilizer X a).subtype Subtype.coe_injective u).symm.trans ht
  have hd := orderOf_dvd_natCard u
  rw [hu] at hd
  have hodd := point_stabilizer_odd c htwo hn hF hΓ a
  rcases hodd with ⟨k, hk⟩
  rcases hd with ⟨l, hl⟩
  omega

private theorem prime_order_element_fixes_unique_point
    (c : Coordinates X F) (htwo : IsMultiplyPretransitive X F 2)
    {n q : ℕ} (hn : n.Prime) (hq : q.Prime) (hq2 : q ≠ 2) (hqn : q ≠ n)
    (hF : Nat.card F = 2 ^ n)
    (hΓ : Nat.card (twoPoint (X := X) (F := F)) = n)
    (r : X) (hr : orderOf r = q) :
    ∃ a : F, r • a = a ∧ ∀ b : F, r • b = b → b = a := by
  let _ : IsMultiplyPretransitive X F 2 := htwo
  let _ : IsPretransitive X F := isPretransitive_of_is_two_pretransitive
  have hcard : q ∣ Nat.card X := by
    have h := orderOf_dvd_natCard r
    rwa [hr] at h
  rcases prime_dvd_mersenne_or_degree c htwo hq hq2 hF hΓ hcard with hM | hnq
  · have hqF : ¬ q ∣ Nat.card F := by
      rw [hF]
      intro h
      have hq2' : q ∣ 2 := hq.dvd_of_dvd_pow h
      rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hq2' with h | h
      · exact hq.ne_one h
      · exact hq2 h
    let R : Subgroup X := Subgroup.zpowers r
    let : Fact q.Prime := ⟨hq⟩
    have hR : IsPGroup q R := by
      apply IsPGroup.of_card (n := 1)
      simp [R, Nat.card_zpowers, hr, pow_one]
    obtain ⟨a, ha⟩ := hR.nonempty_fixed_point_of_prime_not_dvd_card F hqF
    have haR : r • a = a :=
      MulAction.mem_fixedPoints.mp ha ⟨r, Subgroup.mem_zpowers r⟩
    obtain ⟨g, hg⟩ := exists_smul_eq X (0 : F) a
    let y : stabilizer X (0 : F) :=
      ⟨g⁻¹ * r * g, by
        change (g⁻¹ * r * g) • (0 : F) = 0
        simp only [mul_smul, hg, haR]
        rw [← hg, inv_smul_smul]⟩
    have hy : orderOf (y : X) = q := by
      have hconj := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective r
      simpa [y, MulAut.conj_apply, hr] using hconj
    have hyK : (y : X) ∈ c.scalarSubgroup := by
      -- The scalar subgroup is the unique normal Hall complement in the zero stabilizer.
      have hK : Nat.card c.scalarSubgroup = 2 ^ n - 1 := by
        rw [scalar_card c, hF]
      have hB : Nat.card (stabilizer X (0 : F)) = (2 ^ n - 1) * n := by
        rw [c.card_stabilizer, hF, hΓ]
      let K := c.scalarSubgroup.subgroupOf (stabilizer X (0 : F))
      have hKindex : K.index = n := by
        have he := K.card_mul_index
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.scalarSubgroup_le_stabilizer).toEquiv,
          hK, hB] at he
        exact Nat.eq_of_mul_eq_mul_left (hK ▸ Nat.card_pos) he
      let J := (Subgroup.zpowers (y : X)).subgroupOf (stabilizer X (0 : F))
      let : K.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer
        c.scalarSubgroup_le_stabilizer).mpr c.stabilizer_le_scalar_normalizer
      have hle : J ≤ K := by
        apply Subgroup.relIndex_eq_one.mp
        apply Nat.eq_one_of_dvd_coprimes (prime_coprime_mersenne hn)
        · simpa [hKindex] using K.relIndex_dvd_index_of_normal J
        · have hyle : Subgroup.zpowers (y : X) ≤ stabilizer X (0 : F) :=
            Subgroup.zpowers_le.mpr y.property
          have hJ : Nat.card J = q := by
            rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyle).toEquiv,
              Nat.card_zpowers, hy]
          exact (show K.relIndex J ∣ q by simpa [hJ] using K.relIndex_dvd_card J).trans hM
      exact hle (show (⟨(y : X), y.property⟩ : stabilizer X (0 : F)) ∈ J from
        Subgroup.mem_zpowers (y : X))
    obtain ⟨a0, ha0⟩ := hyK
    have ha0' : (y : X) = c.scalar a0 := ha0.symm
    have ha0ne : a0 ≠ 1 := by
      intro h
      have : (y : X) = 1 := by simpa [h] using ha0'
      have : (1 : ℕ) = q := by simpa [this] using hy
      exact hq.ne_one this.symm
    have hfix0 : ∀ x : F, (y : X) • x = x ↔ x = 0 :=
      fun x => by rw [ha0']; exact c.scalar_fixed_iff a0 ha0ne x
    refine ⟨a, haR, ?_⟩
    intro b hb
    have hgb : (y : X) • (g⁻¹ • b) = g⁻¹ • b := by
      calc
        (y : X) • (g⁻¹ • b) = (g⁻¹ * r * g) • (g⁻¹ • b) := by rfl
        _ = (g⁻¹ * r) • b := by simp only [mul_smul, smul_inv_smul]
        _ = g⁻¹ • (r • b) := by rw [mul_smul]
        _ = g⁻¹ • b := by rw [hb]
    have : g⁻¹ • b = 0 := (hfix0 _).mp hgb
    have hga0 : g⁻¹ • a = 0 := by rw [← hg, inv_smul_smul]
    exact MulAction.injective g⁻¹ (this.trans hga0.symm)
  · rcases (Nat.dvd_prime hn).mp hnq with h | h
    · exact (hq.ne_one h).elim
    · exact (hqn h).elim


private theorem inverting_prime_eq_degree
    (c : Coordinates X F) (htwo : IsMultiplyPretransitive X F 2)
    {n q : ℕ} (hn : n.Prime) (hnodd : Odd n) (hq : q.Prime) (hq2 : q ≠ 2)
    (hF : Nat.card F = 2 ^ n)
    (hΓ : Nat.card (twoPoint (X := X) (F := F)) = n)
    (t r : X) (ht : orderOf t = 2) (hr : orderOf r = q)
    (hinv : rightConjugateElem r t = r⁻¹) : q = n := by
  by_contra hqn
  obtain ⟨a, ha, huniq⟩ := prime_order_element_fixes_unique_point
    c htwo hn hq hq2 hqn hF hΓ r hr
  have hmul : r * t = t * r⁻¹ := by
    have h := congrArg (fun x : X => t * x) hinv
    simpa [rightConjugateElem, mul_assoc] using h
  have hfix : r • (t • a) = t • a := by
    rw [← mul_smul, hmul, mul_smul]
    congr 1
    exact inv_smul_eq_iff.mpr ha.symm
  exact no_involution_fixed_point c htwo hnodd hF hΓ t ht a (huniq _ hfix)

omit [Finite X] in
private theorem subgroup_prime_degree_is_sylow
    (c : Coordinates X F) (htwo : IsMultiplyPretransitive X F 2)
    {n : ℕ} (hn : n.Prime) (hnodd : Odd n)
    (hF : Nat.card F = 2 ^ n)
    (hΓ : Nat.card (twoPoint (X := X) (F := F)) = n)
    (H : Subgroup X) (hH : Nat.card H = n) :
    ∃ P : Sylow n X, (P : Subgroup X) = H := by
  let : Fact n.Prime := ⟨hn⟩
  have hidx : H.index = 2 ^ n * (2 ^ n - 1) := by
    have he := H.card_mul_index
    rw [hH, card_group_eq c htwo hF hΓ] at he
    apply Nat.eq_of_mul_eq_mul_left hn.pos
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using he
  have hcop : Nat.Coprime n (2 ^ n * (2 ^ n - 1)) :=
    ((Nat.coprime_two_right.mpr hnodd).pow_right n).mul_right (prime_coprime_mersenne hn)
  have hP : IsPGroup n H := IsPGroup.of_card (n := 1) (by simpa using hH)
  exact ⟨hP.toSylow (by rw [hidx]; exact hn.coprime_iff_not_dvd.mp hcop), rfl⟩

private theorem conjugate_inverter_into_twoPoint_normalizer
    (c : Coordinates X F) (htwo : IsMultiplyPretransitive X F 2)
    {n : ℕ} (hn : n.Prime) (hnodd : Odd n)
    (hF : Nat.card F = 2 ^ n)
    (hΓ : Nat.card (twoPoint (X := X) (F := F)) = n)
    (t r : X) (hr : orderOf r = n)
    (hinv : rightConjugateElem r t = r⁻¹) :
    ∃ u : Subgroup.normalizer (twoPoint (X := X) (F := F) : Set X), IsConj t (u : X) := by
  let : Fact n.Prime := ⟨hn⟩
  obtain ⟨R, hR⟩ := subgroup_prime_degree_is_sylow c htwo hn hnodd hF hΓ
    (Subgroup.zpowers r) (by simpa only [Nat.card_zpowers] using hr)
  obtain ⟨P, hP⟩ := subgroup_prime_degree_is_sylow c htwo hn hnodd hF hΓ
    (twoPoint (X := X) (F := F)) hΓ
  have htN : t ∈ Subgroup.normalizer (Subgroup.zpowers r) := by
    apply (Subgroup.inv_mem_iff _).mp
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    have hh : MulAut.conj t⁻¹ r = r⁻¹ := by
      simpa [MulAut.conj_apply, rightConjugateElem] using hinv
    change Subgroup.zpowers (MulAut.conj t⁻¹ r) = Subgroup.zpowers r
    rw [hh, Subgroup.zpowers_inv]
  obtain ⟨g, hg⟩ := exists_smul_eq X R P
  have hmap : (Subgroup.zpowers r).map (MulAut.conj g).toMonoidHom =
      twoPoint (X := X) (F := F) := by
    have he := congrArg (fun S : Sylow n X => (S : Subgroup X)) hg
    change (R : Subgroup X).map (MulAut.conj g).toMonoidHom = (P : Subgroup X) at he
    rwa [hR, hP] at he
  have hnorm : MulAut.conj g t ∈ Subgroup.normalizer (twoPoint (X := X) (F := F) : Set X) := by
    rw [← hmap, ← Subgroup.map_equiv_normalizer_eq]
    exact ⟨t, htN, rfl⟩
  exact ⟨⟨MulAut.conj g t, hnorm⟩, isConj_iff.mpr ⟨g, rfl⟩⟩

private theorem dihedral_involutions_isConj {n : ℕ} (hn : Odd n)
    (z w : DihedralGroup n) (hz : orderOf z = 2) (hw : orderOf w = 2) : IsConj z w := by
  have hrot : ∀ i : ZMod n, orderOf (DihedralGroup.r i) ∣ n := by
    intro i
    apply orderOf_dvd_of_pow_eq_one
    simp [DihedralGroup.r_pow]
  have hn2 : ¬ 2 ∣ n := hn.not_two_dvd_nat
  cases z with
  | r i => exact (hn2 (hz ▸ hrot i)).elim
  | sr i =>
    cases w with
    | r j => exact (hn2 (hw ▸ hrot j)).elim
    | sr j =>
      apply isConj_of_involutions_odd_product
      · simpa only [hz] using pow_orderOf_eq_one (DihedralGroup.sr i)
      · simpa only [hw] using pow_orderOf_eq_one (DihedralGroup.sr j)
      · rw [DihedralGroup.sr_mul_sr]
        exact hn.of_dvd_nat (hrot _)

private theorem orderOf_eq_of_isConj {G : Type*} [Group G] {x y : G}
    (h : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x).symm

/-- GLS, Volume 4, Chapter 1, Lemma 3.10 (first assertion): all involutions
are conjugate. The displayed normalizer is the normalizer of the literal
stabilizer of zero and one, with its actual dihedral group isomorphism. -/
theorem involutions_isConj
    (c : Coordinates X F) (htwo : IsMultiplyPretransitive X F 2)
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hcore : pCore 2 X = ⊥)
    (_hclosure : c.scalarClosure = ⊤) (hn : n.Prime) (hnodd : Odd n) (_hnlarge : 3 < n)
    (hΓ : Nat.card (twoPoint (X := X) (F := F)) = n)
    (hdihedral : Nonempty ((Subgroup.normalizer (twoPoint (X := X) (F := F) : Set X)) ≃*
      DihedralGroup n)) :
    ∀ z w : X, orderOf z = 2 → orderOf w = 2 → IsConj z w := by
  have hplace : ∀ t : X, orderOf t = 2 →
      ∃ u : Subgroup.normalizer (twoPoint (X := X) (F := F) : Set X), IsConj t (u : X) := by
    intro t ht
    have hti : IsInvolution t := by
      refine ⟨?_, ?_⟩
      · intro h; simp [h] at ht
      · simpa only [ht] using pow_orderOf_eq_one t
    have htn : t ∉ pCore 2 X := by simpa [hcore] using hti.ne_one
    obtain ⟨q, hq, hq2, r, hr, hinv⟩ :=
      involution_outside_twoCore_inverts_odd_prime t hti htn
    have hqn := inverting_prime_eq_degree c htwo hn hnodd hq hq2 hF hΓ t r ht hr hinv
    have hrn : orderOf r = n := hr.trans hqn
    exact conjugate_inverter_into_twoPoint_normalizer c htwo hn hnodd hF hΓ t r hrn hinv
  intro z w hz hw
  obtain ⟨u, hu⟩ := hplace z hz
  obtain ⟨v, hv⟩ := hplace w hw
  obtain ⟨e⟩ := hdihedral
  have hEu : orderOf (e u) = 2 := by
    calc
      orderOf (e u) = orderOf u := orderOf_injective e.toMonoidHom e.injective u
      _ = orderOf (u : X) := (orderOf_injective
        (Subgroup.normalizer _).subtype Subtype.coe_injective u).symm
      _ = orderOf z := (orderOf_eq_of_isConj hu).symm
      _ = 2 := hz
  have hEv : orderOf (e v) = 2 := by
    calc
      orderOf (e v) = orderOf v := orderOf_injective e.toMonoidHom e.injective v
      _ = orderOf (v : X) := (orderOf_injective
        (Subgroup.normalizer _).subtype Subtype.coe_injective v).symm
      _ = orderOf w := (orderOf_eq_of_isConj hv).symm
      _ = 2 := hw
  have huv : IsConj u v := by
    have h := e.symm.toMonoidHom.map_isConj (dihedral_involutions_isConj hnodd (e u) (e v) hEu hEv)
    simpa using h
  exact hu.trans (((Subgroup.normalizer _).subtype.map_isConj huv).trans hv.symm)

end MulAction.SemilinearPointStabilizer.PrimeExclusion
