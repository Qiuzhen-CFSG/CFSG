module

public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryCyclotomic.LinearSylow

/-!
# Quartic primes in six-dimensional linear groups

Multiplication by the units of the quartic field extension on K × F × F
constructs a cyclic subgroup of GL₆(F) of order q⁴−1. For an odd prime
r dividing q²+1, the order of q modulo r is four, so no other factor of
the general linear order is divisible by r. The cyclic subgroup therefore
has prime-to-r index, and every r-subgroup of GL₆(F) is cyclic.

The consumer is the descended exterior-square representation of SU₄(p).
Its scalar-sign kernel vanishes on odd Sylow subgroups. This supplies the
quartic branch of the covering-kernel input in Aschbacher–Smith A.2.17,
printed p.39, by cyclic-Sylow transfer (I.1.2, printed p.407).
-/

open Matrix Subgroup
noncomputable section

namespace Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryCyclotomic

private theorem exists_quartic_torus (F : Type*) [Field F] [Finite F] :
    ∃ C : Subgroup (GL (Fin 6) F), IsCyclic C ∧ Nat.card C = Nat.card F ^ 4 - 1 := by
  let p := ringChar F
  let : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  let K := FiniteField.Extension F p 4
  let b := Module.finBasisOfFinrankEq F (K × (F × F))
    (show Module.finrank F (K × (F × F)) = 6 by
      rw [Module.finrank_prod, Module.finrank_prod,
        FiniteField.finrank_extension, Module.finrank_self])
  let j : Kˣ →* (K × (F × F))ˣ := {
    toFun u := ⟨((u : K), 1), ((u⁻¹ : Kˣ), 1), by ext <;> simp, by ext <;> simp⟩
    map_one' := by apply Units.ext; rfl
    map_mul' u v := by apply Units.ext; ext <;> simp }
  let f : Kˣ →* GL (Fin 6) F :=
    (Units.map (Algebra.leftMulMatrix b).toMonoidHom).comp j
  have hf : Function.Injective f := by
    intro u v h
    apply Units.ext
    exact congrArg Prod.fst (Algebra.leftMulMatrix_injective b (congrArg Units.val h))
  let e := MonoidHom.ofInjective hf
  refine ⟨f.range, e.isCyclic.mp inferInstance, ?_⟩
  rw [← Nat.card_congr e.toEquiv, Nat.card_units, FiniteField.natCard_extension]

private theorem index_quartic {F : Type*} [Field F] [Finite F]
    (C : Subgroup (GL (Fin 6) F)) (hC : Nat.card C = Nat.card F ^ 4 - 1) :
    C.index = Nat.card F ^ 15 * (Nat.card F ^ 6 - 1) * (Nat.card F ^ 5 - 1) *
      (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) * (Nat.card F - 1) := by
  classical
  let := Fintype.ofFinite F
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hpos : 0 < Nat.card F ^ 4 - 1 :=
    Nat.sub_pos_of_lt (one_lt_pow₀ (by omega) (by decide))
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [← hC, C.card_mul_index, hC, Matrix.card_GL_field]
  norm_num [Fin.prod_univ_succ, ← Nat.card_eq_fintype_card]
  have h61 : Nat.card F ^ 6 - Nat.card F =
      Nat.card F * (Nat.card F ^ 5 - 1) := by rw [Nat.mul_sub]; ring_nf
  have h62 : Nat.card F ^ 6 - Nat.card F ^ 2 =
      Nat.card F ^ 2 * (Nat.card F ^ 4 - 1) := by rw [Nat.mul_sub]; ring_nf
  have h63 : Nat.card F ^ 6 - Nat.card F ^ 3 =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) := by rw [Nat.mul_sub]; ring_nf
  have h64 : Nat.card F ^ 6 - Nat.card F ^ 4 =
      Nat.card F ^ 4 * (Nat.card F ^ 2 - 1) := by rw [Nat.mul_sub]; ring_nf
  have h65 : Nat.card F ^ 6 - Nat.card F ^ 5 =
      Nat.card F ^ 5 * (Nat.card F - 1) := by rw [Nat.mul_sub]; ring_nf
  rw [h61, h62, h63, h64, h65]
  ring

private theorem not_dvd_pow_sub_one {q r : ℕ} [Fact r.Prime]
    (hq : 1 ≤ q) (hr2 : r ≠ 2) (hd : r ∣ q ^ 2 + 1)
    (i : ℕ) (hi : ¬ 4 ∣ i) : ¬ r ∣ q ^ i - 1 := by
  intro h
  have he : (q : ZMod r) ^ i = 1 := by
    have hz := (ZMod.natCast_eq_zero_iff (q ^ i - 1) r).mpr h
    simpa only [Nat.cast_sub (Nat.one_le_pow i q hq), Nat.cast_pow,
      Nat.cast_one, sub_eq_zero] using hz
  apply hi
  rw [← orderOf_eq_four_of_dvd_sq_add_one hr2 hd]
  exact orderOf_dvd_of_pow_eq_one he

/-- Quartic cyclotomic primes have cyclic Sylow subgroups in GL₆(q). -/
public theorem gl_six_sylow_isCyclic_of_dvd_sq_add_one
    {F : Type*} [Field F] [Finite F] {r : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) (hq : ¬ r ∣ Nat.card F) (hd : r ∣ Nat.card F ^ 2 + 1)
    (P : Sylow r (GL (Fin 6) F)) : IsCyclic P := by
  obtain ⟨C, hc, hC⟩ := exists_quartic_torus F
  let := hc
  apply sylow_isCyclic_of_cyclic_index C ?_ P
  rw [index_quartic C hC]
  have hr : r.Prime := Fact.out
  have hqpos : 1 ≤ Nat.card F := (Finite.one_lt_card (α := F)).le
  have hn (i : ℕ) (hi : ¬ 4 ∣ i) := not_dvd_pow_sub_one hqpos hr2 hd i hi
  exact hr.not_dvd_mul (hr.not_dvd_mul (hr.not_dvd_mul (hr.not_dvd_mul
    (hr.not_dvd_mul (fun h => hq (hr.dvd_of_dvd_pow h)) (hn 6 (by decide)))
    (hn 5 (by decide))) (hn 3 (by decide))) (hn 2 (by decide))) (by simpa only [pow_one] using hn 1 (by decide))

/-- A faithful six-dimensional matrix action is enough to make the
quartic-primary group cyclic. -/
public theorem isCyclic_of_injective_gl_six
    {F : Type*} [Field F] [Finite F] {r : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) (hq : ¬ r ∣ Nat.card F) (hd : r ∣ Nat.card F ^ 2 + 1)
    {G : Type*} [Group G] (hG : IsPGroup r G)
    (f : G →* GL (Fin 6) F) (hf : Function.Injective f) : IsCyclic G := by
  obtain ⟨P, hP⟩ := (hG.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  let := gl_six_sylow_isCyclic_of_dvd_sq_add_one hr2 hq hd P
  let j : G →* P := f.codRestrict _ (fun g => hP ⟨g, rfl⟩)
  exact isCyclic_of_injective j (fun a b h => hf (congrArg (fun x : P => (x : GL (Fin 6) F)) h))

end Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryCyclotomic
