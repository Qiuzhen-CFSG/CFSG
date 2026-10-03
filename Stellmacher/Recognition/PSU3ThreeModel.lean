module

public import ABG.Basic
public import Theory.GroupTheory.MinimalSimple

/-!
# The characteristic-three unitary recognition interface

The parameter equation in `ABG.IsPSU3 G 3` forces characteristic three and
extension parameter one. Thus this predicate is exactly an isomorphism with
the existing projective special unitary group over `GaloisField 3 2`, with
identity Gram matrix and cube Frobenius. Minimal simplicity transports along
this equivalence.

Source: the definitions `ABG.IsPSU3` and `ABG.unitaryForm`.
-/

/-- ABG's unitary model at parameter three is its standard concrete PSU₃(3). -/
public theorem ABG.isPSU3_three_iff_nonempty_mulEquiv {G : Type*} [Group G] :
    ABG.IsPSU3 G 3 ↔ Nonempty (G ≃* ABG.PSU3 3 1 (by decide)) := by
  constructor
  · rintro ⟨p, n, hp, hn, hpow, ⟨e⟩⟩
    have hpdvd : p ∣ 3 := by
      rw [hpow]
      exact dvd_pow_self p hn
    have hp3 : p = 3 :=
      (Nat.dvd_prime Nat.prime_three).mp hpdvd |>.resolve_left hp.ne_one
    subst p
    have hn1 : n = 1 := by
      apply Nat.pow_right_injective (by decide : 1 < 3)
      simpa using hpow.symm
    subst n
    exact ⟨e⟩
  · rintro ⟨e⟩
    exact ⟨3, 1, Nat.prime_three, by decide, by norm_num, ⟨e⟩⟩

public instance : Finite (ABG.PSU3 3 1 (by decide)) := by
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) (GaloisField 3 2)) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  exact Subtype.finite

/-- Minimal simplicity transfers to the unchanged concrete unitary model. -/
public theorem Stellmacher.Recognition.isMinimalSimple_iff_of_isPSU3_three
    {G : Type*} [Group G] [Finite G] (hG : ABG.IsPSU3 G 3) :
    IsMinimalSimple G ↔ IsMinimalSimple (ABG.PSU3 3 1 (by decide)) := by
  obtain ⟨e⟩ := ABG.isPSU3_three_iff_nonempty_mulEquiv.mp hG
  exact IsMinimalSimple.iff_of_mulEquiv e
