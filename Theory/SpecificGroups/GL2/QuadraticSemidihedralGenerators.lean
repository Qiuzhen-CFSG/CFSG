module
public import Theory.SpecificGroups.GL2.FiniteQuadraticTorus

/-!
# Quadratic semidihedral generators in GL2

If the exact two-part of |F|+1 is 2^n with n≥2, the quadratic torus in
GL2(F) contains a rotation of order 2^(n+1). Its Frobenius reflection is
an external involution conjugating the rotation to its (2^n−1)-st power.
The rotation's half-power is the actual scalar matrix −1, including when
F has order three. These explicit generators are the reusable input to
the semidihedral Sylow construction; no abstract group predicate is used.

The arithmetic lemma derives oddness of |F|, divisibility of |F|²−1,
and the required Frobenius exponent congruence. Choose an element of the
specified order in the cyclic unit group of the actual quadratic extension
and apply `exists_finite_quadratic_torus`. Its half-power squares to one
but is not one, so it is −1; compatibility with base-field scalars gives
the matrix identity. The arithmetic lemma is also exported for the
cardinality computation of the determinant-sign subgroup.

Source: Alperin--Brauer--Gorenstein II.2 Lemma 1, article p17. This extracts
the quadratic construction from `ABG.ChapterII.Section2.LinearSemidihedralSylow`
without changing its hypotheses, conclusions, or extension instances.
-/

namespace Matrix.GeneralLinearGroup

public theorem quadratic_two_part_arithmetic (q n : ℕ) (hn : 2 ≤ n)
    (hd : 2 ^ n ∣ q + 1) (ho : Odd ((q + 1) / 2 ^ n)) :
    Odd q ∧ 2 ^ (n + 1) ∣ q ^ 2 - 1 ∧ q % 2 ^ (n + 1) = 2 ^ n - 1 := by
  have hp : 0 < 2 ^ n := pow_pos (by decide) _
  have h4 : 4 ∣ 2 ^ n := by
    simpa using Nat.pow_dvd_pow 2 hn
  have he := Nat.mul_div_cancel' hd
  obtain ⟨k, hk⟩ := ho
  have hq : q + 1 = 2 ^ n * (2 * k + 1) := by rw [← hk]; exact he.symm
  have hqodd : Odd q := by
    have h2 : 2 ∣ q + 1 := (dvd_trans (by decide : 2 ∣ 4) h4).trans hd
    exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp (even_iff_two_dvd.mpr h2))
  have hmod : q % 2 ^ (n + 1) = 2 ^ n - 1 := by
    rw [pow_succ]
    have hsub : 2 ^ n - 1 + 1 = 2 ^ n := Nat.sub_add_cancel hp
    have heq : q = (2 ^ n - 1) + (2 ^ n * 2) * k := by nlinarith
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
    omega
  refine ⟨hqodd, ?_, hmod⟩
  obtain ⟨r, hr⟩ := hqodd
  refine ⟨r * (2 * k + 1), ?_⟩
  rw [show 2 ^ (n + 1) = 2 ^ n * 2 by rw [pow_succ]]
  have hmul : q ^ 2 = (2 ^ n * 2) * (r * (2 * k + 1)) + 1 := by
    calc
      q ^ 2 = (q - 1) * (q + 1) + 1 := by rw [hr]; simp only [Nat.add_sub_cancel]; ring
      _ = (2 * r) * (2 ^ n * (2 * k + 1)) + 1 := by rw [hr]; simp only [Nat.add_sub_cancel]; rw [← hr, hq]
      _ = _ := by ring
  omega

public theorem finite_quadratic_semidihedral_generators
    (F : Type*) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (n : ℕ) (hn : 2 ≤ n) (hd : 2 ^ n ∣ Nat.card F + 1)
    (ho : Odd ((Nat.card F + 1) / 2 ^ n)) :
    ∃ a w : GL (Fin 2) F,
      orderOf a = 2 ^ (n + 1) ∧ w ^ 2 = 1 ∧ w ∉ Subgroup.zpowers a ∧
      w * a * w⁻¹ = a ^ (2 ^ n - 1) ∧ a ^ (2 ^ n) = scalar (Fin 2) (-1 : Fˣ) := by
  let : Fintype F := Fintype.ofFinite F
  let E := FiniteField.Extension F p 2
  let : Fintype E := Fintype.ofFinite E
  obtain ⟨hq, hdiv, hmod⟩ := quadratic_two_part_arithmetic (Nat.card F) n hn hd ho
  obtain ⟨ρ, w, hi, hw, he, hc, hs⟩ := exists_finite_quadratic_torus F p
  have hecard : Nat.card E = Nat.card F ^ 2 := FiniteField.natCard_extension F p 2
  have hdE : 2 ^ (n + 1) ∣ Nat.card E - 1 := by rw [hecard]; exact hdiv
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Eˣ)
  have hdu : 2 ^ (n + 1) ∣ orderOf u := by rw [hu, Nat.card_units]; exact hdE
  let ζ := u ^ (orderOf u / 2 ^ (n + 1))
  have hz : orderOf ζ = 2 ^ (n + 1) :=
    orderOf_pow_orderOf_div (orderOf_pos u).ne' hdu
  have hhalf : ζ ^ (2 ^ n) = -1 := by
    have hsq : ((ζ ^ (2 ^ n) : Eˣ) : E) ^ 2 = 1 := by
      change (((ζ ^ (2 ^ n)) ^ 2 : Eˣ) : E) = 1
      rw [← pow_mul, ← pow_succ, ← hz, pow_orderOf_eq_one]
      rfl
    rcases sq_eq_one_iff.mp hsq with h1 | hm
    · have hh : ζ ^ (2 ^ n) = 1 := Units.ext h1
      have h := orderOf_dvd_of_pow_eq_one hh
      rw [hz, pow_succ] at h
      have hp : 0 < 2 ^ n := pow_pos (by decide) _
      have hl := Nat.le_of_dvd hp h
      omega
    · exact Units.ext hm
  refine ⟨ρ ζ, w, orderOf_injective ρ hi ζ |>.trans hz, hw, ?_, ?_, ?_⟩
  · intro h
    apply he
    exact (Subgroup.zpowers_le.mpr (show ρ ζ ∈ ρ.range from ⟨ζ, rfl⟩)) h
  · rw [hc, map_pow]
    rw [← pow_mod_orderOf (ρ ζ) (Nat.card F), orderOf_injective ρ hi, hz, hmod]
  · rw [← map_pow, hhalf]
    convert hs (-1 : Fˣ) using 2
    apply Units.ext
    simp

end Matrix.GeneralLinearGroup
