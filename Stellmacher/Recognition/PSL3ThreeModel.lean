module

public import ABG.Basic
public import Theory.SpecificGroups.LinearCoefficientEquiv
public import Theory.GroupTheory.MinimalSimple

/-!
# The actual PSL₃(3) recognition interface

ABG's `IsPSL3 G 3` is equivalent to an isomorphism with the concrete
projective special linear group over `ZMod 3`. The prime-power parameter
must be `3^1`; the canonical equivalence from `GaloisField 3 1` to `ZMod 3`
then acts entrywise on SL and descends through its center. Minimal simplicity
transports along the resulting group equivalence.

Source: `ABG.Basic.IsPSL3` and Mathlib's finite-field model equivalence.
-/

/-- ABG's characteristic-three linear model is the concrete PSL₃(3). -/
public theorem ABG.isPSL3_three_iff_nonempty_mulEquiv {G : Type*} [Group G] :
    ABG.IsPSL3 G 3 ↔
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3)) := by
  constructor
  · rintro ⟨p, n, hp, hn, hpow, ⟨e⟩⟩
    have hpdvd : p ∣ 3 := by
      rw [hpow]
      exact dvd_pow_self p hn
    have hp3 : p = 3 := (Nat.dvd_prime Nat.prime_three).mp hpdvd |>.resolve_left hp.ne_one
    subst p
    have hn1 : n = 1 := by
      apply Nat.pow_right_injective (by decide : 1 < 3)
      simpa using hpow.symm
    subst n
    exact ⟨e.trans (Matrix.ProjectiveSpecialLinearGroup.ringEquiv
      (GaloisField.equivZmodP 3).toRingEquiv)⟩
  · rintro ⟨e⟩
    refine ⟨3, 1, Nat.prime_three, by decide, by norm_num, ?_⟩
    exact ⟨e.trans (Matrix.ProjectiveSpecialLinearGroup.ringEquiv
      (GaloisField.equivZmodP 3).toRingEquiv).symm⟩

/-- Minimal simplicity transfers between the ABG and concrete PSL₃(3) models. -/
public theorem Stellmacher.Recognition.isMinimalSimple_iff_of_isPSL3_three
    {G : Type*} [Group G] [Finite G] (hG : ABG.IsPSL3 G 3) :
    IsMinimalSimple G ↔
      IsMinimalSimple (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3)) := by
  obtain ⟨e⟩ := ABG.isPSL3_three_iff_nonempty_mulEquiv.mp hG
  exact IsMinimalSimple.iff_of_mulEquiv e
