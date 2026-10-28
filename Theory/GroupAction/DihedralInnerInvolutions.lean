module

public import Theory.GroupTheory.AutomorphismTowerSimple
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Index

/-!
# Inner central involutions of dihedral actors

A faithful dihedral actor with rotation order at least four has a central
involution which is a square. If the inner automorphisms have index two,
this actor is conjugation by an involution of the acted-on centerless group.
Every actor fixes that conjugating element. Two adjacent reflections also
supply noncommuting involutions in the original actor group.

The proof uses the half-turn and quarter-turn in the standard dihedral
presentation, together with the fact that all squares lie in an index-two
subgroup. This is the actor-group input to Aschbacher–Smith's PSL₂ fixed-group
generation argument, printed p.566 of `refs/quasithin.pdf`.
-/

public section

open Subgroup

namespace DihedralGroup

private theorem half_turn_data {k : ℕ} (hk : 2 ≤ k) :
    ∃ z j u : DihedralGroup (2 ^ k), z ∈ center (DihedralGroup (2 ^ k)) ∧
      orderOf z = 2 ∧ orderOf j = 2 ∧ j ≠ z ∧ u ^ 2 = z := by
  let a : ZMod (2 ^ k) := (2 ^ (k - 1) : ℕ)
  have ha : a * 2 = 0 := by
    have h : 2 ^ (k - 1) * 2 = 2 ^ k := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
    simpa only [Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_self] using
      congrArg (fun n : ℕ => (n : ZMod (2 ^ k))) h
  have hsq : (r a) ^ 2 = 1 := by simp only [r_pow, Nat.cast_ofNat, ha, r_zero]
  have hne : r a ≠ 1 := by
    intro he
    have he0 : a = 0 := r.inj he
    have hd : 2 ^ k ∣ 2 ^ (k - 1) := (ZMod.natCast_eq_zero_iff _ _).mp he0
    have hlt : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by omega) (by omega)
    exact (not_le_of_gt hlt) (Nat.le_of_dvd (by positivity) hd)
  refine ⟨r a, sr 0, r ((2 ^ (k - 2) : ℕ) : ZMod (2 ^ k)), ?_,
    orderOf_eq_prime hsq hne, orderOf_sr _, ?_, ?_⟩
  · have ha' : -a = a := by
      apply neg_eq_iff_add_eq_zero.mpr
      simpa only [mul_two] using ha
    apply mem_center_iff.mpr
    rintro (i | i)
    · simp only [r_mul_r, add_comm]
    · simp only [sr_mul_r, r_mul_sr, sub_eq_add_neg, ha']
  · intro he
    cases he
  · have h : 2 ^ (k - 2) * 2 = 2 ^ (k - 1) := by
      rw [← pow_succ]
      congr 1
      omega
    simp only [r_pow, Nat.cast_ofNat]
    exact congrArg r (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        congrArg (fun n : ℕ => (n : ZMod (2 ^ k))) h)

/-- Adjacent reflections in a nonabelian dihedral two-group do not commute. -/
theorem exists_noncommuting_involutions {P : Type*} [Group P] {k : ℕ}
    (hk : 2 ≤ k) (e : P ≃* DihedralGroup (2 ^ k)) :
    ∃ a b : P, orderOf a = 2 ∧ orderOf b = 2 ∧ a * b ≠ b * a := by
  refine ⟨e.symm (sr 0), e.symm (sr 1), ?_, ?_, ?_⟩
  · exact (orderOf_injective e.symm.toMonoidHom e.symm.injective _).trans (orderOf_sr _)
  · exact (orderOf_injective e.symm.toMonoidHom e.symm.injective _).trans (orderOf_sr _)
  · intro h
    have he := congrArg e h
    simp only [map_mul, e.apply_symm_apply, sr_mul_sr, sub_zero, zero_sub, r.injEq] at he
    have htwo : (2 : ZMod (2 ^ k)) = 0 := by
      calc
        2 = (1 : ZMod (2 ^ k)) + 1 := by norm_num
        _ = -1 + 1 := congrArg (· + 1) he
        _ = 0 := neg_add_cancel _
    have hd : 2 ^ k ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).mp htwo
    have hbig : 4 ≤ 2 ^ k := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hk
    have := Nat.le_of_dvd (by omega : 0 < (2 : ℕ)) hd
    omega

end DihedralGroup

namespace MulAut

/-- A central inner involution and a distinct reflection in the literal actor group.
The conjugating involution is fixed by every actor. -/
theorem dihedral_inner_involutions {P K : Type*} [Group P] [Group K]
    (f : P →* MulAut K) (hf : Function.Injective f)
    {k : ℕ} (hk : 2 ≤ k) (e : P ≃* DihedralGroup (2 ^ k))
    (hc : center K = ⊥) (hi : (innerSubgroup K).index = 2) :
    ∃ z j : P, ∃ t : K, z ∈ center P ∧ orderOf z = 2 ∧ orderOf j = 2 ∧
      j ≠ z ∧ orderOf t = 2 ∧ f z = conj t ∧ ∀ p : P, f p t = t := by
  obtain ⟨z, j, u, hzc, hz, hj, hjz, hu⟩ := DihedralGroup.half_turn_data hk
  have hzc' : e.symm z ∈ center P := by
    apply mem_center_iff.mpr
    intro p
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_center_iff.mp hzc (e p)
  have hz' : orderOf (e.symm z) = 2 := (orderOf_injective e.symm.toMonoidHom e.symm.injective z).trans hz
  have hinner : f (e.symm z) ∈ innerSubgroup K := by
    rw [← hu, map_pow, map_pow]
    exact sq_mem_of_index_two hi _
  obtain ⟨t, ht⟩ := hinner
  have htord : orderOf t = 2 := by
    rw [← orderOf_injective (conj : K →* MulAut K) (conj_injective_of_center_eq_bot hc) t,
      ht, orderOf_injective f hf, hz']
  refine ⟨e.symm z, e.symm j, t, hzc', hz',
    (orderOf_injective e.symm.toMonoidHom e.symm.injective j).trans hj,
    fun he => hjz (e.symm.injective he), htord, ht.symm, ?_⟩
  intro p
  apply conj_injective_of_center_eq_bot hc
  have hcomm : f p * conj t = conj t * f p := by
    rw [ht, ← map_mul, ← map_mul]
    exact congrArg f (mem_center_iff.mp hzc' p)
  have he : conj (f p t) = f p * conj t * (f p)⁻¹ := by
    ext x
    simp
  rw [he, hcomm, mul_inv_cancel_right]

end MulAut
