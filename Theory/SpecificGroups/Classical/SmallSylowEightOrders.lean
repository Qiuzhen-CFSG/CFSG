module

public import Theory.SpecificGroups.Classical.SmallSylowOrders

/-!
# The odd PSL2 field congruence from a Sylow subgroup of order eight

The fraction-free order equation 2|PSL2(q)| = q(q²-1) identifies the
precise two-part when a Sylow subgroup has order eight. Its field order
is therefore seven or nine modulo sixteen. This is the parameter test
in Aschbacher--Smith F.6.18(6), printed pp.309--310.
-/

public section
open Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.ClassicalSmallSylow

theorem psl2_mod_sixteen_of_sylow_card_eight
    {F : Type*} [Field F] [Finite F] (ho : Odd (Nat.card F))
    (P : Sylow 2 PSL(2,F)) (hP : Nat.card P = 8) :
    Nat.card F % 16 = 7 ∨ Nat.card F % 16 = 9 := by
  have h8 : 8 ∣ Nat.card PSL(2,F) := hP ▸ P.card_subgroup_dvd_card
  have hn16 := not_sixteen_dvd_of_sylow_le_eight P hP.le
  have hm8 := Nat.mod_eq_zero_of_dvd h8
  have hnm16 : Nat.card PSL(2,F) % 16 ≠ 0 := by
    intro h0
    exact hn16 (Nat.dvd_of_mod_eq_zero h0)
  have hm16 : Nat.card PSL(2,F) % 16 = 8 := by omega
  have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice ho
  have hmod : (Nat.card F * (Nat.card F ^ 2 - 1)) % 32 = 16 := by
    rw [← hc]
    omega
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hs : 1 ≤ Nat.card F ^ 2 := by nlinarith
  have hsub : (Nat.card F ^ 2 - 1) % 32 = (Nat.card F ^ 2 + 31) % 32 := by omega
  rw [Nat.mul_mod, hsub, Nat.add_mod, Nat.pow_mod] at hmod
  have hoddmod : Nat.card F % 2 = 1 := Nat.odd_iff.mp ho
  have hb : Nat.card F % 32 < 32 := Nat.mod_lt _ (by decide)
  interval_cases he : Nat.card F % 32 <;>
    norm_num [he] at hmod <;> omega

/-- The two possible odd-PSL2 Sylow profiles below order sixteen. -/
theorem psl2_small_sylow_parameters
    {F : Type*} [Field F] [Finite F]
    (ho : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (P : Sylow 2 PSL(2,F)) (hP : Nat.card P ≤ 8) :
    (Nat.card P = 4 ∧ (Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5)) ∨
    (Nat.card P = 8 ∧ (Nat.card F % 16 = 7 ∨ Nat.card F % 16 = 9)) := by
  obtain ⟨m, hm, ⟨e⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F ho P
  have hc : Nat.card P = 2 * 2 ^ m := by rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hm2 : m ≤ 2 := by
    have hh : 2 ^ m ≤ 2 ^ 2 := by omega
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
  interval_cases m
  · have he : IsElementaryAbelian 2 (DihedralGroup (2 ^ 1)) := by
      change IsElementaryAbelian 2 (DihedralGroup 2)
      exact {
        toIsMulCommutative := IsKleinFour.isMulCommutative
        exponent_dvd_p := by rw [DihedralGroup.exponent]; decide }
    let : IsElementaryAbelian 2 P :=
      IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective
    exact .inl ⟨by simpa using hc, psl2_mod_eight_of_elementary_sylow ho P⟩
  · have hp8 : Nat.card P = 8 := by simpa using hc
    have hodd : Odd (Nat.card F) := by
      obtain ⟨p, f, _, hp, _, hf⟩ := ho
      rw [hf]
      exact hp.pow
    exact .inr ⟨hp8, psl2_mod_sixteen_of_sylow_card_eight hodd P hp8⟩

end Theory.ClassicalSmallSylow
