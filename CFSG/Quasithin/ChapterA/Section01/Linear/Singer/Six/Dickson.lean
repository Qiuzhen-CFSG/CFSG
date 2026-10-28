module

public import CFSG.Quasithin.ChapterA.Section01.Linear.Dickson
public import BenderSuzuki.Converse.PSL2

/-!
# Odd subgroups of GL₂(8)

The corrected Dickson list bounds odd subgroups of PSL₂(8) by nine.
The exceptional cases are excluded by their exact parameters, the affine
case by oddness of its normal two-subgroup, and subfield PSL groups by
their even order. For a subgroup of GL₂(8), the determinant kernel embeds
in SL₂(8), and the actual central quotient is injective in characteristic
two. Its order is at most nine; the determinant image has order at most
seven. Thus every odd subgroup of GL₂(8) has order at most 63.

This is the maximality calculation in Aschbacher–Smith A.1.12, printed
p.22, using the corrected A.1.3. All matrix and quotient comparisons are
actual homomorphisms with proved injectivity.
-/

open BenderSuzuki.MatrixGroups Subgroup
namespace CFSG.Quasithin.ChapterA.Singer.Six

private theorem two_dvd_card_binary_psl (m : ℕ) (hm : m ≠ 0) :
    2 ∣ Nat.card (PSL2MatrixGroup (GaloisField 2 m)) := by
  let S : Sylow 2 (PSL2MatrixGroup (GaloisField 2 m)) := Classical.choice inferInstance
  obtain ⟨e⟩ := Glauberman.Dickson.huppert_II_8_2_a_sylow_equiv_additive
    (GaloisField.card 2 m hm) S
  have hs : Nat.card S = 2 ^ m :=
    (Nat.card_congr e.symm.toEquiv).trans (GaloisField.card 2 m hm)
  have hd : 2 ∣ Nat.card S := by
    rw [hs]
    exact dvd_pow_self _ hm
  exact hd.trans S.toSubgroup.card_subgroup_dvd_card

/-- Dickson's actual PSL₂ alternatives imply the sharp odd-order bound
for a field of eight elements. -/
public theorem odd_psl_eight_card_le_nine
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 8)
    (H : Subgroup (PSL2MatrixGroup F)) (hodd : Odd (Nat.card H)) : Nat.card H ≤ 9 := by
  have hc := CFSG.Quasithin.ChapterA.lemma_A_1_3_corrected
    (p := 2) (f := 3) hF H
  rcases hc with he | hc | hd | ha4 | hs4 | ha5 | haff | hpsl | hpgl
  · obtain ⟨_, m, hm, hcard⟩ := he
    rw [hcard]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hm).trans (by decide)
  · obtain ⟨z, hz, hcard, _⟩ := hc
    norm_num at hz
    rw [hcard]
    rcases hz with hz | hz
    · exact (Nat.le_of_dvd (by decide : 0 < 7) hz).trans (by decide)
    · exact Nat.le_of_dvd (by decide : 0 < 9) hz
  · obtain ⟨z, _, hcard, _⟩ := hd
    exact (hodd.not_two_dvd_nat (hcard ▸ dvd_mul_right 2 z)).elim
  · exact ((by decide : ¬ (2 ≠ 2 ∨ Even 3)) ha4.1).elim
  · norm_num at hs4
  · norm_num at ha5
  · obtain ⟨m, t, _, _, ht, N, C, _, _, hN, _, hC, _, _, φ, ⟨e⟩⟩ := haff
    have hH : Nat.card H = 2 ^ m * t := by
      rw [Nat.card_congr e.toEquiv, SemidirectProduct.card, hN, hC]
    have hm : m = 0 := by
      by_contra hm
      apply hodd.not_two_dvd_nat
      rw [hH]
      exact (dvd_pow_self 2 hm).trans (dvd_mul_right _ _)
    subst m
    have ht7 : t ≤ 7 := Nat.le_of_dvd (by decide) (by simpa using ht)
    simpa only [pow_zero, one_mul, hH] using ht7.trans (by decide : 7 ≤ 9)
  · obtain ⟨m, hm, _, ⟨e⟩⟩ := hpsl
    apply False.elim
    apply hodd.not_two_dvd_nat
    rw [Nat.card_congr e.toEquiv]
    exact two_dvd_card_binary_psl m hm
  · obtain ⟨m, hm, hd, _⟩ := hpgl
    have := dvd_trans (dvd_mul_right 2 m) hd
    norm_num at this

/-- Every odd subgroup of the actual GL₂(8) has order at most 63. -/
public theorem odd_gl_eight_card_le_sixty_three
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 8)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F))
    (hodd : Odd (Nat.card H)) : Nat.card H ≤ 63 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (f := 3) (by
    simpa [Nat.card_eq_fintype_card] using hF)
  let f : H →* Fˣ := Matrix.GeneralLinearGroup.det.comp H.subtype
  let i : f.ker →* Matrix.SpecialLinearGroup (Fin 2) F :=
    { toFun := fun a => ⟨((a.val.val : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F),
        Units.ext_iff.mp a.property⟩
      map_one' := by ext r s; rfl
      map_mul' := by intro a b; ext r s; rfl }
  have hi : Function.Injective i := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro r s
    exact congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F => A r s) hab
  let j := (BenderSuzuki.Converse.pi F).comp i
  have hj : Function.Injective j := BenderSuzuki.Converse.pi_injective.comp hi
  have hkcard : Nat.card f.ker = Nat.card j.range :=
    Nat.card_congr (j.ofInjective hj).toEquiv
  have hk : Nat.card f.ker ≤ 9 := by
    have hoddK : Odd (Nat.card f.ker) := hodd.of_dvd_nat f.ker.card_subgroup_dvd_card
    rw [hkcard] at hoddK ⊢
    exact odd_psl_eight_card_le_nine hF j.range hoddK
  have hFu : Nat.card Fˣ = 7 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hF]
  have hr : Nat.card f.range ≤ 7 :=
    (Nat.card_le_card_of_injective f.range.subtype Subtype.val_injective).trans_eq hFu
  have hcard : Nat.card H = Nat.card f.ker * Nat.card f.range := by
    rw [← Subgroup.index_ker f, f.ker.card_mul_index]
  rw [hcard]
  exact Nat.mul_le_mul hk hr

end CFSG.Quasithin.ChapterA.Singer.Six
