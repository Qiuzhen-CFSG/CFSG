module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.TorusWitness
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.OvergroupModels
public import Mathlib.NumberTheory.Multiplicity

/-!
# Outer four-group witnesses escape the maximal-overgroup models

The low-torus witness has a rotation of order `2*r`, with r an odd prime.
Such a rotation cannot occur in S₄. A full torus normalizer containing the
ambient Sylow has order divisible by eight, so it uses the opposite torus
type and its order is not divisible by r. Both alternatives therefore
exclude containment of the constructed witness.

The maximal-subgroup classification is an explicit input through
`SylowOvergroupModel`; it is not established here. The escape theorem needs
no weak-closure hypothesis for an outer actor.

Source: Aschbacher--Smith E.1.2 and E.1.14(6), printed pp.210 and 214.
-/

public section

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal

open Subgroup GorensteinWalter

private theorem perm_four_powers : ∀ x : Equiv.Perm (Fin 4), x ^ 4 = 1 ∨ x ^ 3 = 1 := by
  decide +kernel

private theorem low_prime_not_dvd_high {q r n : ℕ} (hq : 1 < q) (hr : 3 ≤ r)
    (hlow : (r ∣ q - 1 ∧ Odd ((q - 1) / 2)) ∨ (r ∣ q + 1 ∧ Odd ((q + 1) / 2)))
    (hn : n = q - 1 ∨ n = q + 1) (h8 : 8 ∣ 2 * n) : ¬ r ∣ n := by
  intro hd
  rcases hlow with ⟨hminus, ho⟩ | ⟨hplus, ho⟩
  · rcases hn with rfl | rfl
    · obtain ⟨a, ha⟩ := h8
      obtain ⟨b, hb⟩ := ho
      omega
    · have htwo : r ∣ 2 := by
        have hh := Nat.dvd_sub hd hminus
        convert hh using 1
        omega
      have := Nat.le_of_dvd (by decide : 0 < 2) htwo
      omega
  · rcases hn with rfl | rfl
    · have htwo : r ∣ 2 := by
        have hh := Nat.dvd_sub hplus hd
        convert hh using 1
        omega
      have := Nat.le_of_dvd (by decide : 0 < 2) htwo
      omega
    · obtain ⟨a, ha⟩ := h8
      obtain ⟨b, hb⟩ := ho
      omega

/-- Every outer actor escapes each of the maximal-overgroup models.
The order argument distinguishes the two torus types; S₄ is excluded by
the rotation of order `2*r` in the constructed witness. -/
theorem outer_kleinFour_escape_of_overgroup_model
    (F : Type*) [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    (T : Sylow 2 (PGL2 F)) (A M : Subgroup (PGL2 F)) (hA : IsKleinFour A)
    (hAT : A ≤ T) (hAJ : ¬ A ≤ commutator (PGL2 F))
    (hTM : (T : Subgroup (PGL2 F)) ≤ M) (hM : SylowOvergroupModel F M) :
    ∃ H : Subgroup (PGL2 F), A ≤ H ∧
      (∃ S : Sylow 2 H, (S : Subgroup H) = (T : Subgroup (PGL2 F)).subgroupOf H) ∧
      LocalModel A H ∧ ¬ H ≤ M := by
  let : Finite (PGL2 F) := Finite.of_surjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨H, hAH, hS, r, hr, hro, ⟨eH⟩, hlow⟩ :=
    outer_kleinFour_dihedral_witness F hF hcard T A hA hAT hAJ
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    have := hro.not_two_dvd_nat
    by_contra hh
    have : r = 2 := by omega
    simp_all
  refine ⟨H, hAH, hS, Or.inr ⟨r, hr, hro, ⟨eH⟩⟩, ?_⟩
  intro hHM
  unfold SylowOvergroupModel at hM
  rcases hM with heM | heM
  · obtain ⟨eM⟩ := heM
    let f : H →* Equiv.Perm (Fin 4) := eM.toMonoidHom.comp (inclusion hHM)
    have hf : Function.Injective f := eM.injective.comp (inclusion_injective hHM)
    let x : H := eH.symm (DihedralGroup.r 1)
    have hx : orderOf x = 2 * r := by
      rw [eH.symm.orderOf_eq, DihedralGroup.orderOf_r_one]
    have hfx : orderOf (f x) = 2 * r := (orderOf_injective f hf x).trans hx
    rcases perm_four_powers (f x) with h4 | h3
    · have hd := orderOf_dvd_of_pow_eq_one h4
      rw [hfx] at hd
      have := Nat.le_of_dvd (by decide : 0 < 4) hd
      omega
    · have hd := orderOf_dvd_of_pow_eq_one h3
      rw [hfx] at hd
      have := Nat.le_of_dvd (by decide : 0 < 3) hd
      omega
  · obtain ⟨n, hn, ⟨eM⟩⟩ := heM
    have hq : Odd (Nat.card F) := by
      obtain ⟨p, f, _, hp, _, hq⟩ := hF
      rw [hq]
      exact hp.pow
    have h8G : 2 ^ 3 ∣ Nat.card (PGL2 F) := by
      rw [pgl2_card_formula F]
      exact dvd_mul_of_dvd_right (Nat.eight_dvd_sq_sub_one_of_odd hq) _
    have h8M : 8 ∣ 2 * n := by
      have hd := (T.pow_dvd_card_of_pow_dvd_card h8G).trans (card_dvd_of_le hTM)
      rw [Nat.card_congr eM.toEquiv, DihedralGroup.nat_card] at hd
      exact hd
    have hrM : r ∣ 2 * n := by
      have hd := card_dvd_of_le hHM
      rw [Nat.card_congr eH.toEquiv, Nat.card_congr eM.toEquiv,
        DihedralGroup.nat_card, DihedralGroup.nat_card] at hd
      have hrH : r ∣ 2 * (2 * r) := ⟨4, by ring⟩
      exact hrH.trans hd
    have hrn : r ∣ n := (hr.dvd_mul.mp hrM).resolve_left (by
      intro h
      have := Nat.le_of_dvd (by decide : 0 < 2) h
      omega)
    exact low_prime_not_dvd_high (by omega) hr3 hlow hn h8M hrn

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal
