module

public import Theory.SpecificGroups.PSL2.PrimeQuadraticMaximal

/-!
# Maximality of order-twenty-six subgroups in PSL₂(25)

Dickson's subgroup alternatives leave no proper overgroup of a subgroup of
order 26: cyclic and dihedral alternatives are too small, the exceptional
and proper subfield orders are not divisible by 26, and the Borel orders
have prime-to-five part dividing twelve. This supplies the missing endpoint
for the four-conjugate diagonal-involution construction.

Source: Huppert II.8.27 and the q=25 case of Guralnick--Malle Proposition 4.1.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
namespace Theory.PSL2

theorem isCoatom_of_card_twentySix {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 25) (D : Subgroup (PSL2MatrixGroup F))
    (hD : Nat.card D = 26) : IsCoatom D := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hcard : Nat.card (PSL2MatrixGroup F) = 7800 := by
    have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
      (F := F) (hF ▸ (by decide : Odd 25))
    rw [hF] at hc
    norm_num at hc
    change Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) = 7800
    omega
  have hDne : D ≠ ⊤ := by
    intro ht
    have hc : Nat.card D = Nat.card (PSL2MatrixGroup F) := by rw [ht]; simp
    omega
  refine ⟨hDne, ?_⟩
  intro H hDH
  have hlt : 26 < Nat.card H := by
    rw [← hD]
    by_contra! hge
    exact hDH.ne (eq_of_le_of_card_ge hDH.le hge)
  have hdvd : 26 ∣ Nat.card H := hD ▸ card_dvd_of_le hDH.le
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
      (p := 5) (f := 2) hF H with
    hElem | hCyc | hDih | hA4 | hS4 | hA5 | hBorel | hPSL | hPGL
  · let : IsElementaryAbelian 5 H := hElem
    obtain ⟨m, hm⟩ := (IsElementaryAbelian.isPGroup 5 H).exists_card_eq
    rw [hm] at hdvd
    have hh := ((by decide : Nat.Coprime 26 5).pow_right m).eq_one_of_dvd hdvd
    omega
  · obtain ⟨z, hz, hc, _⟩ := hCyc
    norm_num [hF] at hz
    rcases hz with hz | hz
    all_goals
      have hb := Nat.le_of_dvd (by decide) hz
      omega
  · obtain ⟨z, hz, hc, _⟩ := hDih
    norm_num [hF] at hz
    rcases hz with hz | hz
    all_goals
      have hb := Nat.le_of_dvd (by decide) hz
      omega
  · obtain ⟨_, ⟨f⟩⟩ := hA4
    have hc := Nat.card_congr f.toEquiv
    rw [nat_card_alternatingGroup, Nat.card_fin] at hc
    norm_num at hc
    omega
  · obtain ⟨_, ⟨f⟩⟩ := hS4
    have hc := Nat.card_congr f.toEquiv
    rw [Nat.card_perm, Nat.card_fin] at hc
    norm_num at hc
    omega
  · obtain ⟨_, ⟨f⟩⟩ := hA5
    have hc := Nat.card_congr f.toEquiv
    rw [nat_card_alternatingGroup, Nat.card_fin] at hc
    norm_num at hc
    rw [hc] at hdvd
    norm_num at hdvd
  · obtain ⟨m, t, _, ht, N, C, hN, _, hcN, _, hcC, hdisj, hsup⟩ := hBorel
    let : N.Normal := hN
    have hc : Nat.card H = 5 ^ m * t := by
      have hh := card_sup_eq_mul_of_normalizes_of_disjoint N C
        (by rw [N.normalizer_eq_top]; exact le_top) hdisj
      simpa [hsup, hcN, hcC] using hh
    rw [hc] at hdvd
    have hd := ((by decide : Nat.Coprime 26 5).pow_right m).dvd_of_dvd_mul_left hdvd
    have hlow := Nat.le_of_dvd (hcC ▸ Nat.card_pos (α := C)) hd
    norm_num at ht
    have hhigh := Nat.le_of_dvd (by decide) ht
    omega
  · obtain ⟨m, hm0, hmdiv, ⟨f⟩⟩ := hPSL
    have hm : m = 1 ∨ m = 2 := (Nat.dvd_prime Nat.prime_two).mp hmdiv
    have hmcard := GaloisField.card 5 m hm0
    have hmOdd : Odd (Nat.card (GaloisField 5 m)) := hmcard ▸ (by decide : Odd 5).pow
    have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
      (F := GaloisField 5 m) hmOdd
    rw [hmcard, ← Nat.card_congr f.toEquiv] at hc
    rcases hm with rfl | rfl
    · have hh : Nat.card H = 60 := by norm_num at hc; omega
      rw [hh] at hdvd
      norm_num at hdvd
    · apply eq_top_of_card_eq H
      rw [hcard]
      norm_num at hc
      omega
  · obtain ⟨m, hm0, hmdiv, ⟨f⟩⟩ := hPGL
    have hb := Nat.le_of_dvd (by decide : 0 < 2) hmdiv
    have hm1 : m = 1 := by omega
    have hc := GorensteinWalter.pgl2_card_formula (GaloisField 5 m)
    rw [GaloisField.card 5 m hm0, ← Nat.card_congr f.toEquiv, hm1] at hc
    norm_num at hc
    rw [hc] at hdvd
    norm_num at hdvd

end Theory.PSL2
