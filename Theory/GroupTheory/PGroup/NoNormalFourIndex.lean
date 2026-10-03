module

public import Theory.GroupTheory.PGroup.NoNormalFourAction

/-!
# The index of a cyclic self-centralizing subgroup

In a finite two-group without normal elementary four-groups, a cyclic normal
self-centralizing subgroup has index at most two. Its subgroup of order four
has the same centralizer: a nontrivial element of the centralizer quotient
would lift to a modular action, which can be adjusted to an involution and
would give a normal four-group. The action on the subgroup of order four
then bounds the index by two.

This is the cyclic subgroup step in GLS, Number 2, Chapter C, Lemma 10.11.
-/

open Subgroup

private theorem zpowers_pow_normal {P : Type*} [Group P]
    (a : P) [(zpowers a).Normal] (k : ℕ) : (zpowers (a ^ k)).Normal := by
  constructor
  intro x hx g
  have hga : g * a * g⁻¹ ∈ zpowers a := Normal.conj_mem inferInstance a (mem_zpowers a) g
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hga
  have hmap : (zpowers (a ^ k)).map (MulAut.conj g).toMonoidHom ≤ zpowers (a ^ k) := by
    rw [MonoidHom.map_zpowers]
    apply zpowers_le.mpr
    change MulAut.conj g (a ^ k) ∈ zpowers (a ^ k)
    rw [map_pow, MulAut.conj_apply, ← hj]
    have heq : (a ^ j) ^ k = (a ^ k) ^ j := by
      simp only [← zpow_natCast, ← zpow_mul, mul_comm]
    rw [heq]
    exact zpow_mem (mem_zpowers _) _
  exact hmap (mem_map_of_mem _ hx)

private theorem mem_of_square_mem_of_centralizes_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4)
    (A : Subgroup P) [A.Normal] [IsCyclic A]
    (hC : centralizer (A : Set P) ≤ A)
    (a g : P) (n : ℕ) (hn : 2 ≤ n) (hA : A = zpowers a)
    (ha : orderOf a = 2 ^ n) (hg2 : g ^ 2 ∈ A)
    (hgb : g * a ^ (2 ^ (n - 2)) * g⁻¹ = a ^ (2 ^ (n - 2))) : g ∈ A := by
  classical
  by_contra hgA
  have haA : a ∈ A := by rw [hA]; exact mem_zpowers a
  have hconjA : g * a * g⁻¹ ∈ zpowers a := by
    rw [← hA]
    exact Normal.conj_mem inferInstance a haA g
  obtain ⟨r, hr, har⟩ := Finset.mem_image.mp
    (mem_zpowers_iff_mem_range_orderOf.mp hconjA)
  have hrlt : r < 2 ^ n := by simpa [ha] using Finset.mem_range.mp hr
  let b := a ^ (2 ^ (n - 2))
  have hsplit4 : 2 ^ n = 2 ^ (n - 2) * 4 := by
    conv_lhs => rw [show n = (n - 2) + 2 by omega]
    rw [pow_add]; norm_num
  have hb : orderOf b = 4 := by
    have hh := orderOf_pow_orderOf_div (Nat.ne_of_gt (orderOf_pos a))
      (show 4 ∣ orderOf a by rw [ha, hsplit4]; exact dvd_mul_left _ _)
    simpa [ha, hsplit4, b] using hh
  have hr4 : r % 4 = 1 := by
    have hp : b ^ r = b ^ 1 := by
      calc
        b ^ r = (a ^ r) ^ (2 ^ (n - 2)) := by dsimp [b]; rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ = MulAut.conj g (a ^ (2 ^ (n - 2))) := by rw [map_pow, MulAut.conj_apply, har]
        _ = b := hgb
        _ = b ^ 1 := (pow_one b).symm
    simpa [hb, Nat.ModEq] using pow_eq_pow_iff_modEq.mp hp
  have hr1 : r ≠ 1 := by
    intro hh
    apply hgA
    apply hC
    intro y hy
    rw [hA] at hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    have hc : Commute a g := by
      have hc' : g * a * g⁻¹ = a := by simpa [hh] using har.symm
      exact (mul_inv_eq_iff_eq_mul.mp hc').symm
    exact (hc.zpow_left k).eq
  have hn3 : 3 ≤ n := by
    by_contra hh
    have hn2 : n = 2 := by omega
    norm_num [hn2] at hrlt
    omega
  have haction (d : P) (hd : d ∈ A) : g * d * g⁻¹ = d ^ r := by
    rw [hA] at hd
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hd)
    change MulAut.conj g (a ^ k) = _
    rw [map_pow, MulAut.conj_apply, ← har, ← pow_mul, ← pow_mul, Nat.mul_comm]
  have hrr : 2 ^ n ∣ r * r - 1 := by
    have hp : a ^ (r * r) = a := by
      calc
        a ^ (r * r) = MulAut.conj g (a ^ r) := by rw [map_pow, MulAut.conj_apply, ← har, pow_mul]
        _ = MulAut.conj g (MulAut.conj g a) := by congr 1
        _ = (g ^ 2) * a * (g ^ 2)⁻¹ := by simp only [MulAut.conj_apply, pow_two]; group
        _ = a := mul_inv_eq_iff_eq_mul.mpr ((A.le_centralizer hg2) a haA).symm
    rw [← ha]
    have hrpos : 1 ≤ r := by omega
    exact (Nat.modEq_iff_dvd' (by nlinarith : 1 ≤ r * r)).mp
      (pow_eq_pow_iff_modEq.mp (hp.trans (pow_one a).symm)).symm
  have hrval := Nat.eq_one_add_two_pow_of_mod_four n r hn3 hrlt hr4 hr1 hrr
  have hsplit : 2 ^ n = 2 ^ (n - 1) * 2 := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp
    (mem_zpowers_iff_mem_range_orderOf.mp (hA ▸ hg2))
  have htmod : 2 ^ n ∣ t * (r - 1) := by
    have hp : a ^ (t * r) = a ^ t := by
      calc
        a ^ (t * r) = (a ^ t) ^ r := pow_mul _ _ _
        _ = g * (g ^ 2) * g⁻¹ := by rw [ht, ← haction (g ^ 2) hg2]
        _ = g ^ 2 := by simp only [pow_two]; group
        _ = a ^ t := ht.symm
    have hlower : t ≤ t * r := Nat.le_mul_of_pos_right t (by omega)
    have hh := (Nat.modEq_iff_dvd' hlower).mp (pow_eq_pow_iff_modEq.mp hp).symm
    simpa [ha, Nat.mul_sub_left_distrib] using hh
  have hteven : 2 ∣ t := by
    rw [hrval, show 1 + 2 ^ (n - 1) - 1 = 2 ^ (n - 1) by omega,
      hsplit, Nat.mul_comm t] at htmod
    exact (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2 ^ (n - 1))).mp htmod
  obtain ⟨v, hv⟩ := hteven
  let u := 1 + 2 ^ (n - 2)
  have hodd : Nat.Coprime 2 u := by
    apply Nat.coprime_two_left.mpr
    exact Odd.add_even (by decide : Odd (1 : ℕ))
      (Nat.even_pow.mpr ⟨by decide, by omega⟩)
  obtain ⟨dA, hdA⟩ := ((hP.to_subgroup A).powEquiv hodd).surjective
    ((⟨a, haA⟩ : A) ^ v)⁻¹
  let d : P := dA
  have hd : d ∈ A := dA.property
  have hdPow : d ^ u = (a ^ v)⁻¹ := congrArg Subtype.val hdA
  have hexp : 1 + r = u * 2 := by
    have hh : 2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by
      conv_lhs => rw [show n - 1 = (n - 2) + 1 by omega]
      rw [pow_succ]
    rw [hrval, hh]
    dsimp [u]
    omega
  let e := d * g
  have he : e ^ 2 = 1 := by
    calc
      e ^ 2 = d * (g * d * g⁻¹) * g ^ 2 := by dsimp [e]; simp only [pow_two]; group
      _ = d ^ (1 + r) * a ^ t := by rw [haction d hd, ← ht, pow_add, pow_one]
      _ = (d ^ u) ^ 2 * (a ^ v) ^ 2 := by rw [hexp, pow_mul, hv, Nat.mul_comm 2 v, pow_mul]
      _ = 1 := by rw [hdPow, inv_pow, inv_mul_cancel]
  have heA : e ∉ A := by
    intro hh
    apply hgA
    have hmem := A.mul_mem (A.inv_mem hd) hh
    simpa [e] using hmem
  have heact : e * a * e⁻¹ = a ^ r := by
    calc
      e * a * e⁻¹ = d * (g * a * g⁻¹) * d⁻¹ := by dsimp [e]; group
      _ = d * a ^ r * d⁻¹ := by rw [← har]
      _ = a ^ r := mul_inv_eq_iff_eq_mul.mpr ((A.le_centralizer hd) (a ^ r) (A.pow_mem haA r)).symm
  exact hno (hP.exists_normal_four_of_twist A hC a e n hn3 hA ha he heA
    (by simpa [hrval] using heact))

private theorem le_of_square_mem_imp
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (A C : Subgroup P) [A.Normal]
    (h : ∀ g ∈ C, g ^ 2 ∈ A → g ∈ A) : C ≤ A := by
  let K := A.subgroupOf C
  rcases ((hP.to_subgroup C).to_quotient K).card_eq_or_dvd with hcard | hdiv
  · have htop : K = ⊤ := index_eq_one.mp hcard
    exact subgroupOf_eq_top.mp htop
  · obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := C ⧸ K) 2 hdiv
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K q
    have hg2 : g ^ 2 ∈ K := by
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' K) (g ^ 2) = 1
      rw [map_pow, ← hq, pow_orderOf_eq_one]
    have hgA : (g : P) ∈ A := h g g.property hg2
    have hgq : (QuotientGroup.mk' K) g = 1 := (QuotientGroup.eq_one_iff _).mpr hgA
    rw [hgq, orderOf_one] at hq
    contradiction

private theorem kernel_le_centralizer
    {P : Type*} [Group P] (B : Subgroup P) [B.Normal] :
    (MulAut.conjNormal : P →* MulAut B).ker ≤ centralizer (B : Set P) := by
  intro g hg b hb
  have hh := congrArg (fun t : MulAut B => (t ⟨b, hb⟩ : P))
    (MonoidHom.mem_ker.mp hg)
  change g * b * g⁻¹ = b at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

namespace IsPGroup

/-- A cyclic normal self-centralizing subgroup in a finite two-group without
normal elementary four-groups has index at most two. -/
public theorem index_le_two_of_cyclic_normal_selfCentralizing_of_no_normal_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4)
    (A : Subgroup P) [A.Normal] [IsCyclic A]
    (hC : centralizer (A : Set P) ≤ A) : A.index ≤ 2 := by
  classical
  obtain ⟨a, haA⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  obtain ⟨n, hn⟩ := (hP.to_subgroup A).exists_card_eq
  have ha : orderOf a = 2 ^ n := by rw [← Nat.card_zpowers, haA, hn]
  by_cases hn2 : 2 ≤ n
  · let b := a ^ (2 ^ (n - 2))
    let B := zpowers b
    let : (zpowers a).Normal := haA.symm ▸ inferInstance
    let : B.Normal := zpowers_pow_normal a _
    have hsplit : 2 ^ n = 2 ^ (n - 2) * 4 := by
      conv_lhs => rw [show n = (n - 2) + 2 by omega]
      rw [pow_add]; norm_num
    have hBcard : Nat.card B = 4 := by
      rw [Nat.card_zpowers]
      have hh := orderOf_pow_orderOf_div (Nat.ne_of_gt (orderOf_pos a))
        (show 4 ∣ orderOf a by rw [ha, hsplit]; exact dvd_mul_left _ _)
      simpa [ha, hsplit, b] using hh
    let f : P →* MulAut B := MulAut.conjNormal
    have hker : f.ker ≤ A := by
      apply le_of_square_mem_imp hP A f.ker
      intro g hg hg2
      apply mem_of_square_mem_of_centralizes_four hP hno A hC a g n hn2 haA.symm ha hg2
      exact mul_inv_eq_iff_eq_mul.mpr
        ((kernel_le_centralizer B hg) b (mem_zpowers b)).symm
    calc
      A.index ≤ f.ker.index := index_antitone hker
      _ = Nat.card f.range := index_ker f
      _ ≤ Nat.card (MulAut B) := card_le_card_group _
      _ = 2 := by rw [IsCyclic.card_mulAut, hBcard]; decide
  · let f : P →* MulAut A := MulAut.conjNormal
    have hker : f.ker ≤ A := (kernel_le_centralizer A).trans hC
    calc
      A.index ≤ f.ker.index := index_antitone hker
      _ = Nat.card f.range := index_ker f
      _ ≤ Nat.card (MulAut A) := card_le_card_group _
      _ ≤ 2 := by
        rw [IsCyclic.card_mulAut, hn]
        have hnlt : n < 2 := by omega
        interval_cases n <;> norm_num

end IsPGroup
