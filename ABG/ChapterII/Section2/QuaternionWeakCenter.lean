module
public import ABG.ChapterII.Section2.Defs
public import ABG.ChapterII.Section1.NormalQuaternionCenter

/-!
# Weak closure of quaternion central subgroups

Every subgroup of the center of a generalized quaternion subgroup R is
weakly closed in R with respect to its finite ambient group. R need not
be normal or Sylow. The quaternion calculation makes every square-one
element central. Since the center has order two, a conjugate central
subgroup lying in R lies in that center and has the same cardinality,
so it equals the original subgroup.

This supplies the weak-closure clause of the enlarged Q-group definition
in ABG II.2 Definition 3 for the quaternion kernel in II.3 Lemma 3,
article page 30. The separate kernel theorem retains the necessary
wreathed overgroup and normal-index hypotheses.
-/

namespace ABG

private theorem quaternion_square_one_central {m : ℕ} (hm : 2 ≤ m)
    (x : QuaternionGroup m) (hx : x ^ 2 = 1) :
    x ∈ Subgroup.center (QuaternionGroup m) := by
  let : NeZero m := ⟨by omega⟩
  cases x with
  | a i =>
    have hi : i + i = 0 := QuaternionGroup.a.inj (by simpa only [pow_two,
      QuaternionGroup.a_mul_a, QuaternionGroup.one_def] using hx)
    have hi' : -i = i := by linear_combination -hi
    apply Subgroup.mem_center_iff.mpr
    rintro (j | j)
    · simp [add_comm]
    · simp [sub_eq_add_neg, hi', add_comm]
  | xa i =>
    have hi : (m : ZMod (2 * m)) = 0 := QuaternionGroup.a.inj (by
      simpa only [pow_two, QuaternionGroup.xa_mul_xa, add_sub_cancel_right,
        QuaternionGroup.one_def] using hx)
    have hv := congrArg ZMod.val hi
    simp only [ZMod.val_natCast, ZMod.val_zero,
      Nat.mod_eq_of_lt (by omega : m < 2 * m)] at hv
    omega

public theorem hasWeaklyClosedCenterSubgroups_of_quaternion {H : Type*} [Group H] [Finite H]
    (R : Subgroup H) (hR : IsGeneralizedQuaternionGroup R) :
    HasWeaklyClosedCenterSubgroups R := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hR
  have hn2 : 2 ≤ 2 ^ n := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) hn
  have hc : Nat.card (Subgroup.center R) = 2 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact QuaternionGroup.card_center_of_two_le _ hn2
  have hca : Nat.card (subgroupCenter R) = 2 := by
    rw [subgroupCenter, Subgroup.card_map_of_injective R.subtype_injective, hc]
  intro Z hZ
  refine ⟨hZ.trans (Subgroup.map_subtype_le _), ?_⟩
  intro g hg
  have hcard : Nat.card (BenderSuzuki.PFchapter1section1.rightConjugate Z g) = Nat.card Z := by
    change Nat.card (Z.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card Z
    exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hle : BenderSuzuki.PFchapter1section1.rightConjugate Z g ≤ subgroupCenter R := by
    intro x hx
    have hxx : x ^ 2 = 1 := by
      have hdiv := Subgroup.card_dvd_of_le hZ
      rw [hca] at hdiv
      have hd : Nat.card (BenderSuzuki.PFchapter1section1.rightConjugate Z g) ∣ 2 := by
        rwa [hcard]
      have hp := orderOf_dvd_iff_pow_eq_one.mp
        ((orderOf_dvd_natCard (⟨x, hx⟩ : BenderSuzuki.PFchapter1section1.rightConjugate Z g)).trans hd)
      exact congrArg Subtype.val hp
    let y : R := ⟨x, hg hx⟩
    have hy : y ^ 2 = 1 := Subtype.ext hxx
    have he : e y ∈ Subgroup.center (QuaternionGroup (2 ^ n)) :=
      quaternion_square_one_central hn2 (e y) (by simpa using congrArg e hy)
    refine ⟨y, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro z
    apply e.injective
    simpa using Subgroup.mem_center_iff.mp he (e z)
  have hd := Subgroup.card_dvd_of_le hZ
  rw [hca, Nat.dvd_prime Nat.prime_two] at hd
  rcases hd with hd | hd
  · have hbot : Z = ⊥ := Subgroup.card_eq_one.mp hd
    have hbot' : BenderSuzuki.PFchapter1section1.rightConjugate Z g = ⊥ :=
      Subgroup.card_eq_one.mp (hcard.trans hd)
    exact hbot'.trans hbot.symm
  · have heq : Z = subgroupCenter R := Subgroup.eq_of_le_of_card_ge hZ (by omega)
    exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).trans heq.symm


end ABG

