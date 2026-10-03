module
public import ABG.ChapterII.Section1.Center
public import Theory.GroupTheory.CentralInvolutionFourNormalizer
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators
public import Mathlib.GroupTheory.Nilpotent
/-!
# The canonical four subgroup of a quasi-dihedral group

For the semidihedral generators with `n ≥ 4`, the half-order power `z` and
`b` generate a Klein four-group `U`. It is precisely the centralizer of `b`:
normal forms and the odd-factor cancellation in `half_order_dvd` force any
commuting cyclic exponent to be a multiple of the half-order. The four
elements are `1, z, b, z*b`; the shared commuting-involution construction
in `KleinFourGenerators` supplies the order and exponent.

When the group has order `2^n`, the finite 2-group normalizer condition makes
`N(U)` strictly larger than `U`. Conjugation fixes the central involution
`z`, so the generic four-subgroup normalizer lemma gives `[N(U):U] = 2`.
The inclusion `C(U) ≤ C(b) = U` proves the centralizer assertion.

These explicit-generator results establish the local structure needed in
ABG Chapter II, §1, Lemma 1(ii), article page 9 of
`refs/latex/alperin-brauer-gorenstein.tex`. Conjugacy of arbitrary four
subgroups to this representative is proved separately.
-/

namespace ABG.QuasiDihedral
variable {G : Type*} [Group G]
/-- The centralizer of the outer involution lies in the canonical four subgroup. -/
public theorem centralizer_b_le_four {n : ℕ} (hn : 4 ≤ n) (a b : G)
    (ha : orderOf a = 2 ^ (n - 1)) (hb : orderOf b = 2)
    (hconj : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) :
    Subgroup.centralizer ({b} : Set G) ≤
      Subgroup.closure ({a ^ (2 ^ (n - 2)), b} : Set G) := by
  let U := Subgroup.closure ({a ^ (2 ^ (n - 2)), b} : Set G)
  have hzU : a ^ (2 ^ (n - 2)) ∈ U := Subgroup.subset_closure (by simp)
  have hbU : b ∈ U := Subgroup.subset_closure (by simp)
  have hb2 : b ^ 2 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hp : 2 ≤ 2 ^ (n - 2) := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hpow (i : ℕ) (hc : a ^ i * b = b * a ^ i) : a ^ i ∈ U := by
    have heq : a ^ i = a ^ ((2 ^ (n - 2) - 1) * i) := by
      apply mul_right_cancel (b := b)
      rw [← move_pow a b _ hconj i]
      exact hc
    have hd : 2 ^ (n - 1) ∣ (2 ^ (n - 2) - 2) * i := by
      have h := (pow_eq_pow_iff_modEq.mp heq).dvd'
      rw [ha] at h
      convert h using 1
      simp only [show 2 ^ (n - 2) - 2 = 2 ^ (n - 2) - 1 - 1 by omega,
        Nat.sub_mul, one_mul]
    obtain ⟨j, hj⟩ := half_order_dvd hn hd
    rw [hj, pow_mul]
    exact U.pow_mem hzU j
  intro x hx
  have hc := Subgroup.mem_centralizer_singleton_iff.mp hx
  obtain ⟨i, _, rfl | rfl⟩ := normal_form a b _ _ (by positivity) ha hb2 hconj hgen x
  · exact hpow i hc
  · apply U.mul_mem _ hbU
    apply hpow
    apply mul_right_cancel (b := b)
    simpa only [mul_assoc] using hc

/-- The canonical four subgroup is exactly the centralizer of the outer involution. -/
public theorem centralizer_b_eq_four {n : ℕ} (hn : 4 ≤ n) (a b : G)
    (ha : orderOf a = 2 ^ (n - 1)) (hb : orderOf b = 2)
    (hconj : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) :
    Subgroup.centralizer ({b} : Set G) =
      Subgroup.closure ({a ^ (2 ^ (n - 2)), b} : Set G) := by
  apply le_antisymm (centralizer_b_le_four hn a b ha hb hconj hgen)
  apply (Subgroup.closure_le _).mpr
  intro x hx
  rcases (by simpa using hx : x = a ^ (2 ^ (n - 2)) ∨ x = b) with rfl | rfl
  · apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact (Subgroup.mem_center_iff.mp (half_order_pow_mem_center hn a b ha hb hconj hgen) b).symm
  · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
/-- The central involution and the outer involution generate a Klein four subgroup. -/
public theorem four_representative_isKleinFour {n : ℕ} (hn : 4 ≤ n) (a b : G)
    (ha : orderOf a = 2 ^ (n - 1)) (hb : orderOf b = 2)
    (hconj : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) :
    IsKleinFour (Subgroup.closure ({a ^ (2 ^ (n - 2)), b} : Set G)) := by
  let z := a ^ (2 ^ (n - 2))
  have hz : orderOf z = 2 := half_order_pow_orderOf hn ha
  have hzb : z ≠ b := by
    intro h
    apply generators_not_commute hn ha hconj
    rw [← h]
    exact Commute.self_pow a _
  have hcomm : Commute z b := (Subgroup.mem_center_iff.mp
    (half_order_pow_mem_center hn a b ha hb hconj hgen) b).symm
  exact Subgroup.isKleinFour_closure_pair_of_orderOf z b hz hb hzb hcomm

private theorem four_lt_normalizer {n : ℕ} (hn : 4 ≤ n)
    (hcard : Nat.card G = 2 ^ n) (U : Subgroup G) (hU : IsKleinFour U) :
    U < Subgroup.normalizer (U : Set G) := by
  let : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hp : IsPGroup 2 G := IsPGroup.iff_card.mpr ⟨n, hcard⟩
  let : Group.IsNilpotent G := hp.isNilpotent
  apply Group.normalizerCondition_of_isNilpotent U
  apply lt_top_iff_ne_top.mpr
  intro heq
  have h := hU.card_four
  rw [heq, Subgroup.card_top, hcard] at h
  have hn' : 4 < 2 ^ n := by
    calc
      4 < 2 ^ 4 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  omega

/-- The canonical four subgroup is self-centralizing with normalizer index two (ABG II.1.1(ii)). -/
public theorem four_representative_local {n : ℕ} (hn : 4 ≤ n)
    (hcard : Nat.card G = 2 ^ n) (a b : G)
    (ha : orderOf a = 2 ^ (n - 1)) (hb : orderOf b = 2)
    (hconj : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) :
    let U := Subgroup.closure ({a ^ (2 ^ (n - 2)), b} : Set G)
    IsKleinFour U ∧ Subgroup.centralizer (U : Set G) ≤ U ∧
      U.relIndex (Subgroup.normalizer (U : Set G)) = 2 := by
  let U := Subgroup.closure ({a ^ (2 ^ (n - 2)), b} : Set G)
  let z := a ^ (2 ^ (n - 2))
  have hzU : z ∈ U := Subgroup.subset_closure (by simp [z])
  have hbU : b ∈ U := Subgroup.subset_closure (by simp)
  have hU : IsKleinFour U := four_representative_isKleinFour hn a b ha hb hconj hgen
  let : IsKleinFour U := hU
  have hC : Subgroup.centralizer ({b} : Set G) ≤ U :=
    centralizer_b_le_four hn a b ha hb hconj hgen
  refine ⟨hU, (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbU)).trans hC, ?_⟩
  have hz : orderOf z = 2 := half_order_pow_orderOf hn ha
  have hz1 : z ≠ 1 := by intro h; simp [h] at hz
  have hb1 : b ≠ 1 := by intro h; simp [h] at hb
  have hbz : b ≠ z := by
    intro h
    apply generators_not_commute hn ha hconj
    rw [h]
    exact Commute.self_pow a _
  exact Subgroup.four_normalizer_relIndex U z b hzU hbU hz1 hb1 hbz
    (half_order_pow_mem_center hn a b ha hb hconj hgen) hC
    (SetLike.exists_of_lt (four_lt_normalizer hn hcard U hU))
end ABG.QuasiDihedral
