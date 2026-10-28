module

public import Theory.AlgebraicGroup.RootData.PositiveRootCollection

/-!
# Positive mixed roots in a rank-two plane

For roots `alpha` and `delta` whose sum `gamma` is a root, this module
classifies every root having strictly positive integral coordinates in the
ordered plane spanned by `alpha` and `delta`.  Under the finite,
crystallographic, reduced root-system hypotheses, the coordinate set is one
of the six familiar rank-two positive-root tables.  The base-membership and
positivity assumptions record the orientation required by downstream
positive-root collection arguments; the classification itself only needs the
displayed root-sum identity.

The proof first applies Mathlib's finite crystallographic pairing alternative
to `(alpha, delta)`, `(gamma, alpha)`, and `(gamma, delta)`.  Pairing bounds
exclude all but the listed coordinates.  Root strings construct the extra
roots in the non-simply-laced cases, while reflection through `gamma` relates
the two possible off-diagonal roots in the remaining `G2` configuration.

This is the standard rank-two root-system calculation used in the finite
Chevalley parameter-word argument.  Its source content is the reduced
crystallographic rank-two classification, here derived from the pairing and
root-string APIs rather than assumed as a separate classification hypothesis.
-/

namespace Theory.AlgebraicGroup

open Set

private lemma pairingIn_bounds
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsCrystallographic] [P.IsReduced]
    (i j : ι) :
    -3 ≤ P.pairingIn ℤ i j ∧ P.pairingIn ℤ i j ≤ 3 := by
  have h := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i j
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  omega

private lemma pairingIn_eq_of_root_eq_nat_smul_add
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsCrystallographic]
    {alpha delta rho tau : ι} {i j : ℕ}
    (hroot : P.root rho =
      (i : R) • P.root alpha + (j : R) • P.root delta) :
    P.pairingIn ℤ rho tau =
      (i : ℤ) * P.pairingIn ℤ alpha tau +
        (j : ℤ) * P.pairingIn ℤ delta tau := by
  have hrootZ : P.root rho =
      (i : ℤ) • P.root alpha + (j : ℤ) • P.root delta := by
    simpa only [natCast_zsmul, Nat.cast_smul_eq_nsmul R] using hroot
  simpa [smul_eq_mul] using
    (P.pairingIn_eq_add_of_root_eq_smul_add_smul
      (S := ℤ) (j := tau) hrootZ)

private lemma chainTopCoeff_ge_of_pairingIn_eq_neg
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsCrystallographic]
    {i j : ι} (hLI : LinearIndependent R ![P.root i, P.root j])
    {n : ℕ} (hpair : P.pairingIn ℤ j i = -(n : ℤ)) :
    n ≤ P.chainTopCoeff i j := by
  have hdiff := P.chainBotCoeff_sub_chainTopCoeff hLI
  omega

private lemma root_add_two_notMem_of_pairingIn_nonneg
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsCrystallographic] [P.IsReduced]
    {i j : ι} (hLI : LinearIndependent R ![P.root i, P.root j])
    (hpair : 0 ≤ P.pairingIn ℤ j i) :
    P.root j + 2 • P.root i ∉ Set.range P.root := by
  intro hroot
  have htop : 2 ≤ P.chainTopCoeff i j :=
    (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hLI).mp hroot
  have hdiff := P.chainBotCoeff_sub_chainTopCoeff hLI
  have hlen := P.chainBotCoeff_add_chainTopCoeff_le_three (i := i) (j := j)
  omega

private lemma root_eq_cast_smul_add_of_root_eq_nsmul_add
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) {alpha delta rho : ι} {i j : ℕ}
    (hroot : P.root rho = i • P.root alpha + j • P.root delta) :
    P.root rho = (i : R) • P.root alpha + (j : R) • P.root delta := by
  simpa only [Nat.cast_smul_eq_nsmul R] using hroot

public theorem rankTwoPositiveMixedRootCoordinates_cases
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (base : P.Base) {alpha delta gamma : ι}
    (hdelta : delta ∈ base.support)
    (halpha : base.IsPos alpha) (hgamma : base.IsPos gamma)
    (hadd : P.root gamma = P.root alpha + P.root delta) :
    {ij : Nat × Nat | 0 < ij.1 ∧ 0 < ij.2 ∧
        ∃ rho, P.root rho =
          (ij.1 : R) • P.root alpha + (ij.2 : R) • P.root delta} =
        ({(1, 1)} : Set (Nat × Nat)) ∨
      {ij : Nat × Nat | 0 < ij.1 ∧ 0 < ij.2 ∧
        ∃ rho, P.root rho =
          (ij.1 : R) • P.root alpha + (ij.2 : R) • P.root delta} =
        ({(1, 1), (1, 2)} : Set (Nat × Nat)) ∨
      {ij : Nat × Nat | 0 < ij.1 ∧ 0 < ij.2 ∧
        ∃ rho, P.root rho =
          (ij.1 : R) • P.root alpha + (ij.2 : R) • P.root delta} =
        ({(1, 1), (2, 1)} : Set (Nat × Nat)) ∨
      {ij : Nat × Nat | 0 < ij.1 ∧ 0 < ij.2 ∧
        ∃ rho, P.root rho =
          (ij.1 : R) • P.root alpha + (ij.2 : R) • P.root delta} =
        ({(1, 1), (1, 2), (1, 3), (2, 3)} : Set (Nat × Nat)) ∨
      {ij : Nat × Nat | 0 < ij.1 ∧ 0 < ij.2 ∧
        ∃ rho, P.root rho =
          (ij.1 : R) • P.root alpha + (ij.2 : R) • P.root delta} =
        ({(1, 1), (2, 1), (3, 1), (3, 2)} : Set (Nat × Nat)) ∨
      {ij : Nat × Nat | 0 < ij.1 ∧ 0 < ij.2 ∧
        ∃ rho, P.root rho =
          (ij.1 : R) • P.root alpha + (ij.2 : R) • P.root delta} =
        ({(1, 1), (1, 2), (2, 1)} : Set (Nat × Nat)) := by
  have hcontext : delta ∈ base.support ∧ base.IsPos alpha ∧ base.IsPos gamma :=
    ⟨hdelta, halpha, hgamma⟩
  clear hcontext hdelta halpha hgamma
  let S : Set (Nat × Nat) :=
    {ij | 0 < ij.1 ∧ 0 < ij.2 ∧
      ∃ rho, P.root rho =
        (ij.1 : R) • P.root alpha + (ij.2 : R) • P.root delta}
  change S = ({(1, 1)} : Set (Nat × Nat)) ∨
    S = ({(1, 1), (1, 2)} : Set (Nat × Nat)) ∨
    S = ({(1, 1), (2, 1)} : Set (Nat × Nat)) ∨
    S = ({(1, 1), (1, 2), (1, 3), (2, 3)} : Set (Nat × Nat)) ∨
    S = ({(1, 1), (2, 1), (3, 1), (3, 2)} : Set (Nat × Nat)) ∨
    S = ({(1, 1), (1, 2), (2, 1)} : Set (Nat × Nat))
  let a := P.pairingIn ℤ alpha delta
  let b := P.pairingIn ℤ delta alpha
  let c := P.pairingIn ℤ alpha gamma
  let d := P.pairingIn ℤ delta gamma
  have hsum : P.root delta + P.root alpha ∈ Set.range P.root :=
    ⟨gamma, by simpa [add_comm] using hadd⟩
  have hLI : LinearIndependent R ![P.root delta, P.root alpha] :=
    P.linearIndependent_of_add_mem_range_root' hsum
  have hLIsymm : LinearIndependent R ![P.root alpha, P.root delta] :=
    P.linearIndependent_of_add_mem_range_root' ⟨gamma, hadd⟩
  have hga : P.pairingIn ℤ gamma alpha = 2 + b := by
    rw [P.pairingIn_eq_add_of_root_eq_add hadd, P.pairingIn_same]
  have hgd : P.pairingIn ℤ gamma delta = a + 2 := by
    rw [P.pairingIn_eq_add_of_root_eq_add hadd, P.pairingIn_same]
  have hcd : c + d = 2 := by
    have h := P.pairingIn_eq_add_of_root_eq_add (S := ℤ) (j := gamma) hadd
    rw [P.pairingIn_same] at h
    exact h.symm
  have hp := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed alpha delta
  have hpga := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed gamma alpha
  have hpgd := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed gamma delta
  change (a, b) ∈ _ at hp
  change (P.pairingIn ℤ gamma alpha, c) ∈ _ at hpga
  change (P.pairingIn ℤ gamma delta, d) ∈ _ at hpgd
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hp hpga hpgd
  have hcases :
      (a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 1) ∨
      (a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1) ∨
      (a = -1 ∧ b = -1 ∧ c = 1 ∧ d = 1) ∨
      (a = -2 ∧ b = -1 ∧ c = 2 ∧ d = 0) ∨
      (a = -1 ∧ b = -2 ∧ c = 0 ∧ d = 2) ∨
      (a = -3 ∧ b = -1 ∧ c = 3 ∧ d = -1) ∨
      (a = -1 ∧ b = -3 ∧ c = -1 ∧ d = 3) := by
    rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp
    all_goals rcases hp with ⟨ha, hb⟩
    all_goals subst a; subst b
    all_goals simp_all
    all_goals omega
  have bounds : ∀ {i j : ℕ} {rho : ι},
      P.root rho = (i : R) • P.root alpha + (j : R) • P.root delta →
      (-3 ≤ 2 * (i : ℤ) + b * (j : ℤ) ∧
        2 * (i : ℤ) + b * (j : ℤ) ≤ 3) ∧
      (-3 ≤ a * (i : ℤ) + 2 * (j : ℤ) ∧
        a * (i : ℤ) + 2 * (j : ℤ) ≤ 3) ∧
      (-3 ≤ c * (i : ℤ) + d * (j : ℤ) ∧
        c * (i : ℤ) + d * (j : ℤ) ≤ 3) := by
    intro i j rho hroot
    have hpa := pairingIn_eq_of_root_eq_nat_smul_add P (tau := alpha) hroot
    have hpd := pairingIn_eq_of_root_eq_nat_smul_add P (tau := delta) hroot
    have hpg := pairingIn_eq_of_root_eq_nat_smul_add P (tau := gamma) hroot
    have hpaBounds := pairingIn_bounds P rho alpha
    have hpdBounds := pairingIn_bounds P rho delta
    have hpgBounds := pairingIn_bounds P rho gamma
    rw [P.pairingIn_same] at hpa hpd
    change P.pairingIn ℤ rho alpha =
      (i : ℤ) * 2 + (j : ℤ) * b at hpa
    change P.pairingIn ℤ rho delta =
      (i : ℤ) * a + (j : ℤ) * 2 at hpd
    change P.pairingIn ℤ rho gamma =
      (i : ℤ) * c + (j : ℤ) * d at hpg
    have hpa' : P.pairingIn ℤ rho alpha =
        2 * (i : ℤ) + b * (j : ℤ) := hpa.trans (by ring)
    have hpd' : P.pairingIn ℤ rho delta =
        a * (i : ℤ) + 2 * (j : ℤ) := hpd.trans (by ring)
    have hpg' : P.pairingIn ℤ rho gamma =
        c * (i : ℤ) + d * (j : ℤ) := hpg.trans (by ring)
    omega
  have hmem11 : (1, 1) ∈ S := by
    exact ⟨by omega, by omega, gamma, by simpa using hadd⟩
  have tableOne (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c = 1) (hd : d = 1) :
      S = ({(1, 1)} : Set (Nat × Nat)) := by
    have hnot12 : P.root alpha + 2 • P.root delta ∉ Set.range P.root :=
      root_add_two_notMem_of_pairingIn_nonneg P hLI ha
    have hnot21 : P.root delta + 2 • P.root alpha ∉ Set.range P.root :=
      root_add_two_notMem_of_pairingIn_nonneg P hLIsymm hb
    ext ij
    constructor
    · rcases ij with ⟨i, j⟩
      rintro ⟨hi, hj, rho, hrho⟩
      have hbounds := bounds hrho
      simp [hc, hd] at hbounds
      have hij : (i = 1 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨
          (i = 2 ∧ j = 1) := by
        omega
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp
      · exfalso
        apply hnot12
        exact ⟨rho, by
          simpa only [Nat.cast_one, one_smul, Nat.cast_smul_eq_nsmul R] using hrho⟩
      · exfalso
        apply hnot21
        exact ⟨rho, by
          simpa only [Nat.cast_one, one_smul, Nat.cast_smul_eq_nsmul R, add_comm]
            using hrho⟩
    · intro hij
      have : ij = (1, 1) := by simpa using hij
      subst ij
      exact hmem11
  rcases hcases with hzero | hone | hnegone | hnegTwoOne | hnegOneTwo |
      hnegThreeOne | hnegOneThree
  · rcases hzero with ⟨ha, hb, hc, hd⟩
    exact Or.inl (tableOne (by omega) (by omega) hc hd)
  · rcases hone with ⟨ha, hb, hc, hd⟩
    exact Or.inl (tableOne (by omega) (by omega) hc hd)
  · rcases hnegone with ⟨ha, hb, hc, hd⟩
    let _ := P.indexNeg
    have reflect12to21 : ∀ {eta : ι},
        P.root eta = ((1 : ℕ) : R) • P.root alpha + ((2 : ℕ) : R) • P.root delta →
        ∃ theta, P.root theta =
          ((2 : ℕ) : R) • P.root alpha + ((1 : ℕ) : R) • P.root delta := by
      intro eta heta
      have hpair := pairingIn_eq_of_root_eq_nat_smul_add P
        (R := R) (M := M) (N := N)
        (alpha := alpha) (delta := delta) (rho := eta)
        (i := 1) (j := 2) (tau := gamma) heta
      change P.pairingIn ℤ eta gamma = 1 * c + 2 * d at hpair
      have hpair3 : P.pairingIn ℤ eta gamma = 3 := by
        simp [hc, hd] at hpair
        exact hpair
      refine ⟨-(P.reflectionPerm gamma eta), ?_⟩
      rw [P.indexNeg_neg, P.root_reflectionPerm, P.reflection_apply_self,
        P.root_reflectionPerm, P.reflection_apply_root' ℤ]
      rw [neg_sub]
      rw [hpair3]
      rw [hadd, heta]
      module
    have reflect21to12 : ∀ {eta : ι},
        P.root eta = ((2 : ℕ) : R) • P.root alpha + ((1 : ℕ) : R) • P.root delta →
        ∃ theta, P.root theta =
          ((1 : ℕ) : R) • P.root alpha + ((2 : ℕ) : R) • P.root delta := by
      intro eta heta
      have hpair := pairingIn_eq_of_root_eq_nat_smul_add P
        (R := R) (M := M) (N := N)
        (alpha := alpha) (delta := delta) (rho := eta)
        (i := 2) (j := 1) (tau := gamma) heta
      change P.pairingIn ℤ eta gamma = 2 * c + 1 * d at hpair
      have hpair3 : P.pairingIn ℤ eta gamma = 3 := by
        simp [hc, hd] at hpair
        exact hpair
      refine ⟨-(P.reflectionPerm gamma eta), ?_⟩
      rw [P.indexNeg_neg, P.root_reflectionPerm, P.reflection_apply_self,
        P.root_reflectionPerm, P.reflection_apply_root' ℤ]
      rw [neg_sub]
      rw [hpair3]
      rw [hadd, heta]
      module
    by_cases h12 : P.root alpha + 2 • P.root delta ∈ Set.range P.root
    · obtain ⟨eta, heta⟩ := h12
      have hetaR : P.root eta =
          ((1 : ℕ) : R) • P.root alpha + ((2 : ℕ) : R) • P.root delta := by
        exact root_eq_cast_smul_add_of_root_eq_nsmul_add P
          (alpha := alpha) (delta := delta) (rho := eta) (i := 1) (j := 2) (by
            simpa only [one_nsmul] using heta)
      obtain ⟨theta, hthetaR⟩ := reflect12to21 hetaR
      have hmem12 : (1, 2) ∈ S := by
        refine ⟨by omega, by omega, eta, ?_⟩
        change P.root eta = ((1 : ℕ) : R) • P.root alpha + ((2 : ℕ) : R) • P.root delta
        exact hetaR
      have hmem21 : (2, 1) ∈ S := by
        refine ⟨by omega, by omega, theta, ?_⟩
        change P.root theta = ((2 : ℕ) : R) • P.root alpha + ((1 : ℕ) : R) • P.root delta
        exact hthetaR
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
      ext ij
      constructor
      · rcases ij with ⟨i, j⟩
        rintro ⟨hi, hj, rho, hrho⟩
        have hbounds := bounds hrho
        simp [ha, hb, hc, hd] at hbounds
        have hij : (i = 1 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨
            (i = 2 ∧ j = 1) := by
          omega
        rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
      · intro hij
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hij
        rcases hij with h | h | h
        · subst ij
          exact hmem11
        · subst ij
          exact hmem12
        · subst ij
          exact hmem21
    · refine Or.inl ?_
      ext ij
      constructor
      · rcases ij with ⟨i, j⟩
        rintro ⟨hi, hj, rho, hrho⟩
        have hbounds := bounds hrho
        simp [ha, hb, hc, hd] at hbounds
        have hij : (i = 1 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨
            (i = 2 ∧ j = 1) := by
          omega
        rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp
        · exfalso
          apply h12
          exact ⟨rho, by
            simpa only [Nat.cast_one, one_smul, Nat.cast_smul_eq_nsmul R] using hrho⟩
        · exfalso
          apply h12
          have hrho' : P.root rho =
              ((2 : ℕ) : R) • P.root alpha + ((1 : ℕ) : R) • P.root delta := by
            simpa only using hrho
          obtain ⟨theta, htheta⟩ := reflect21to12 hrho'
          exact ⟨theta, by
            simpa only [Nat.cast_one, one_smul, Nat.cast_smul_eq_nsmul R]
              using htheta⟩
      · intro hij
        have : ij = (1, 1) := by simpa using hij
        subst ij
        exact hmem11
  · rcases hnegTwoOne with ⟨ha, hb, hc, hd⟩
    have htop : 2 ≤ P.chainTopCoeff delta alpha :=
      chainTopCoeff_ge_of_pairingIn_eq_neg P hLI (n := 2) (by
        change a = -(2 : ℤ)
        exact ha)
    have hroot12 :=
      (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hLI).mpr htop
    obtain ⟨eta, heta⟩ := hroot12
    have hmem12 : (1, 2) ∈ S := by
      refine ⟨by omega, by omega, eta, ?_⟩
      exact root_eq_cast_smul_add_of_root_eq_nsmul_add P
        (alpha := alpha) (delta := delta) (rho := eta) (i := 1) (j := 2) (by
          simpa only [one_nsmul] using heta)
    refine Or.inr (Or.inl ?_)
    ext ij
    constructor
    · rcases ij with ⟨i, j⟩
      rintro ⟨hi, hj, rho, hrho⟩
      have hbounds := bounds hrho
      simp [ha, hb, hc, hd] at hbounds
      have hij : (i = 1 ∧ j = 1) ∨ (i = 1 ∧ j = 2) := by
        omega
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    · intro hij
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hij
      rcases hij with h | h
      · subst ij
        exact hmem11
      · subst ij
        exact hmem12
  · rcases hnegOneTwo with ⟨ha, hb, hc, hd⟩
    have htop : 2 ≤ P.chainTopCoeff alpha delta :=
      chainTopCoeff_ge_of_pairingIn_eq_neg P hLIsymm (n := 2) (by
        change b = -(2 : ℤ)
        exact hb)
    have hroot21 :=
      (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hLIsymm).mpr htop
    obtain ⟨eta, heta⟩ := hroot21
    have hmem21 : (2, 1) ∈ S := by
      refine ⟨by omega, by omega, eta, ?_⟩
      simpa only [add_comm] using
        (root_eq_cast_smul_add_of_root_eq_nsmul_add P
          (alpha := delta) (delta := alpha) (rho := eta) (i := 1) (j := 2) (by
            simpa only [one_nsmul] using heta))
    refine Or.inr (Or.inr (Or.inl ?_))
    ext ij
    constructor
    · rcases ij with ⟨i, j⟩
      rintro ⟨hi, hj, rho, hrho⟩
      have hbounds := bounds hrho
      simp [ha, hb, hc, hd] at hbounds
      have hij : (i = 1 ∧ j = 1) ∨ (i = 2 ∧ j = 1) := by
        omega
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    · intro hij
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hij
      rcases hij with h | h
      · subst ij
        exact hmem11
      · subst ij
        exact hmem21
  · rcases hnegThreeOne with ⟨ha, hb, hc, hd⟩
    have htop3 : 3 ≤ P.chainTopCoeff delta alpha :=
      chainTopCoeff_ge_of_pairingIn_eq_neg P hLI (n := 3) (by
        change a = -(3 : ℤ)
        exact ha)
    have htop2 : 2 ≤ P.chainTopCoeff delta alpha := by omega
    obtain ⟨eta, heta⟩ :=
      (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hLI).mpr htop2
    obtain ⟨theta, htheta⟩ :=
      (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hLI).mpr htop3
    have hetaR : P.root eta =
        ((1 : ℕ) : R) • P.root alpha + ((2 : ℕ) : R) • P.root delta := by
      exact root_eq_cast_smul_add_of_root_eq_nsmul_add P
        (alpha := alpha) (delta := delta) (rho := eta) (i := 1) (j := 2) (by
          simpa only [one_nsmul] using heta)
    have hthetaR : P.root theta =
        ((1 : ℕ) : R) • P.root alpha + ((3 : ℕ) : R) • P.root delta := by
      exact root_eq_cast_smul_add_of_root_eq_nsmul_add P
        (alpha := alpha) (delta := delta) (rho := theta) (i := 1) (j := 3) (by
          simpa only [one_nsmul] using htheta)
    have hetaAlpha : P.pairingIn ℤ eta alpha = 0 := by
      have hpair := pairingIn_eq_of_root_eq_nat_smul_add P
        (R := R) (M := M) (N := N)
        (alpha := alpha) (delta := delta) (rho := eta)
        (i := 1) (j := 2) (tau := alpha) hetaR
      rw [P.pairingIn_same] at hpair
      change P.pairingIn ℤ eta alpha = 1 * 2 + 2 * b at hpair
      simp [hb] at hpair
      exact hpair
    have hAlphaEta : P.pairingIn ℤ alpha eta = 0 :=
      (P.pairingIn_eq_zero_iff (S := ℤ)).mp hetaAlpha
    have hDeltaEta : P.pairingIn ℤ delta eta = 1 := by
      have hpair := pairingIn_eq_of_root_eq_nat_smul_add P
        (R := R) (M := M) (N := N)
        (alpha := alpha) (delta := delta) (rho := eta)
        (i := 1) (j := 2) (tau := eta) hetaR
      rw [P.pairingIn_same] at hpair
      simp [hAlphaEta] at hpair
      omega
    have etaUpper : ∀ {i j : ℕ} {rho : ι},
        P.root rho = (i : R) • P.root alpha + (j : R) • P.root delta →
        j ≤ 3 := by
      intro i j rho hroot
      have hpair := pairingIn_eq_of_root_eq_nat_smul_add P (tau := eta) hroot
      have hpairBounds := pairingIn_bounds P rho eta
      rw [hAlphaEta, hDeltaEta] at hpair
      omega
    let _ := P.indexNeg
    let zeta := -(P.reflectionPerm gamma alpha)
    have hc' : P.pairingIn ℤ alpha gamma = 3 := hc
    have hzeta : P.root zeta =
        ((2 : ℕ) : R) • P.root alpha + ((3 : ℕ) : R) • P.root delta := by
      dsimp only [zeta]
      rw [P.indexNeg_neg, P.root_reflectionPerm, P.reflection_apply_self,
        P.root_reflectionPerm, P.reflection_apply_root' ℤ]
      rw [neg_sub]
      rw [hc']
      rw [hadd]
      module
    have hmem12 : (1, 2) ∈ S := by
      refine ⟨by omega, by omega, eta, ?_⟩
      change P.root eta = ((1 : ℕ) : R) • P.root alpha + ((2 : ℕ) : R) • P.root delta
      exact hetaR
    have hmem13 : (1, 3) ∈ S := by
      refine ⟨by omega, by omega, theta, ?_⟩
      change P.root theta = ((1 : ℕ) : R) • P.root alpha + ((3 : ℕ) : R) • P.root delta
      exact hthetaR
    have hmem23 : (2, 3) ∈ S := by
      refine ⟨by omega, by omega, zeta, ?_⟩
      change P.root zeta = ((2 : ℕ) : R) • P.root alpha + ((3 : ℕ) : R) • P.root delta
      exact hzeta
    refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    ext ij
    constructor
    · rcases ij with ⟨i, j⟩
      rintro ⟨hi, hj, rho, hrho⟩
      have hbounds := bounds hrho
      simp [ha, hb, hc, hd] at hbounds
      have hj3 := etaUpper hrho
      have hij : (i = 1 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨
          (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 3) := by
        omega
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    · intro hij
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hij
      rcases hij with h | h | h | h
      · subst ij
        exact hmem11
      · subst ij
        exact hmem12
      · subst ij
        exact hmem13
      · subst ij
        exact hmem23
  · rcases hnegOneThree with ⟨ha, hb, hc, hd⟩
    have htop3 : 3 ≤ P.chainTopCoeff alpha delta :=
      chainTopCoeff_ge_of_pairingIn_eq_neg P hLIsymm (n := 3) (by
        change b = -(3 : ℤ)
        exact hb)
    have htop2 : 2 ≤ P.chainTopCoeff alpha delta := by omega
    obtain ⟨eta, heta⟩ :=
      (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hLIsymm).mpr htop2
    obtain ⟨theta, htheta⟩ :=
      (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hLIsymm).mpr htop3
    have hetaR : P.root eta =
        ((2 : ℕ) : R) • P.root alpha + ((1 : ℕ) : R) • P.root delta := by
      simpa only [add_comm] using
        (root_eq_cast_smul_add_of_root_eq_nsmul_add P
          (alpha := delta) (delta := alpha) (rho := eta) (i := 1) (j := 2) (by
            simpa only [one_nsmul] using heta))
    have hthetaR : P.root theta =
        ((3 : ℕ) : R) • P.root alpha + ((1 : ℕ) : R) • P.root delta := by
      simpa only [add_comm] using
        (root_eq_cast_smul_add_of_root_eq_nsmul_add P
          (alpha := delta) (delta := alpha) (rho := theta) (i := 1) (j := 3) (by
            simpa only [one_nsmul] using htheta))
    have hetaDelta : P.pairingIn ℤ eta delta = 0 := by
      have hpair := pairingIn_eq_of_root_eq_nat_smul_add P
        (R := R) (M := M) (N := N)
        (alpha := alpha) (delta := delta) (rho := eta)
        (i := 2) (j := 1) (tau := delta) hetaR
      rw [P.pairingIn_same] at hpair
      change P.pairingIn ℤ eta delta = 2 * a + 1 * 2 at hpair
      simp [ha] at hpair
      exact hpair
    have hDeltaEta : P.pairingIn ℤ delta eta = 0 :=
      (P.pairingIn_eq_zero_iff (S := ℤ)).mp hetaDelta
    have hAlphaEta : P.pairingIn ℤ alpha eta = 1 := by
      have hpair := pairingIn_eq_of_root_eq_nat_smul_add P
        (R := R) (M := M) (N := N)
        (alpha := alpha) (delta := delta) (rho := eta)
        (i := 2) (j := 1) (tau := eta) hetaR
      rw [P.pairingIn_same] at hpair
      simp [hDeltaEta] at hpair
      omega
    have etaUpper : ∀ {i j : ℕ} {rho : ι},
        P.root rho = (i : R) • P.root alpha + (j : R) • P.root delta →
        i ≤ 3 := by
      intro i j rho hroot
      have hpair := pairingIn_eq_of_root_eq_nat_smul_add P (tau := eta) hroot
      have hpairBounds := pairingIn_bounds P rho eta
      rw [hAlphaEta, hDeltaEta] at hpair
      omega
    let _ := P.indexNeg
    let zeta := -(P.reflectionPerm gamma delta)
    have hd' : P.pairingIn ℤ delta gamma = 3 := hd
    have hzeta : P.root zeta =
        ((3 : ℕ) : R) • P.root alpha + ((2 : ℕ) : R) • P.root delta := by
      dsimp only [zeta]
      rw [P.indexNeg_neg, P.root_reflectionPerm, P.reflection_apply_self,
        P.root_reflectionPerm, P.reflection_apply_root' ℤ]
      rw [neg_sub]
      rw [hd']
      rw [hadd]
      module
    have hmem21 : (2, 1) ∈ S := by
      refine ⟨by omega, by omega, eta, ?_⟩
      change P.root eta = ((2 : ℕ) : R) • P.root alpha + ((1 : ℕ) : R) • P.root delta
      exact hetaR
    have hmem31 : (3, 1) ∈ S := by
      refine ⟨by omega, by omega, theta, ?_⟩
      change P.root theta = ((3 : ℕ) : R) • P.root alpha + ((1 : ℕ) : R) • P.root delta
      exact hthetaR
    have hmem32 : (3, 2) ∈ S := by
      refine ⟨by omega, by omega, zeta, ?_⟩
      change P.root zeta = ((3 : ℕ) : R) • P.root alpha + ((2 : ℕ) : R) • P.root delta
      exact hzeta
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    ext ij
    constructor
    · rcases ij with ⟨i, j⟩
      rintro ⟨hi, hj, rho, hrho⟩
      have hbounds := bounds hrho
      simp [ha, hb, hc, hd] at hbounds
      have hi3 := etaUpper hrho
      have hij : (i = 1 ∧ j = 1) ∨ (i = 2 ∧ j = 1) ∨
          (i = 3 ∧ j = 1) ∨ (i = 3 ∧ j = 2) := by
        omega
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    · intro hij
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hij
      rcases hij with h | h | h | h
      · subst ij
        exact hmem11
      · subst ij
        exact hmem21
      · subst ij
        exact hmem31
      · subst ij
        exact hmem32

end Theory.AlgebraicGroup
