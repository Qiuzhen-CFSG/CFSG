module

public import Theory.SpecificGroups.PSL2.PrimeQuadraticMaximal

/-!
# Maximality for the low-two-part torus in the diagonal calculation

The nonsplit case uses the proved prime/quadratic criterion of order q+1.
The split case has prime field order: an odd square is 1 modulo 4, so its
split torus cannot have odd half-order. Dickson's classification gives
maximality of a subgroup of order p-1 by the same order comparisons.

Source: Huppert II.8.27; Guralnick--Malle, Classification of 2F-modules I,
Proposition 4.1, manuscript pp.8--9.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration.Diagonal
open Subgroup BenderSuzuki.MatrixGroups

private theorem large_divisor_sixty {n : ℕ} (hl : 24 < n) (hu : n < 60)
    (hd : n ∣ 60) : n = 30 := by
  interval_cases n <;> norm_num at *

/-- The split torus normalizer is maximal at the prime parameters needed here. -/
theorem isCoatom_of_card_eq_prime_pred {F : Type*} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hF : Nat.card F = p) (hlarge : 25 < p)
    (D : Subgroup (PSL2MatrixGroup F)) (hD : Nat.card D = p - 1) :
    IsCoatom D := by
  classical
  have hqodd : Odd (Nat.card F) := hF ▸ ho
  have hcard := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) hqodd
  rw [hF] at hcard
  have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 := by
    apply Nat.gcd_eq_right_iff_dvd.mpr
    obtain ⟨k, hk⟩ := hqodd
    exact ⟨k, by omega⟩
  have hcop : (p - 1).Coprime p := by
    exact ((Nat.coprime_self_sub_right (by omega : 1 ≤ p)).mpr
      (Nat.coprime_one_right _)).symm
  have hDne : D ≠ ⊤ := by
    intro ht
    have hc : Nat.card (PSL2MatrixGroup F) = p - 1 := by
      simpa [ht] using hD
    rw [hc] at hcard
    have hs : 4 ≤ p ^ 2 - 1 := by
      have : 5 ≤ p ^ 2 := by nlinarith
      omega
    have hb := Nat.mul_le_mul_left p hs
    omega
  refine ⟨hDne, ?_⟩
  intro H hDH
  have hlt : p - 1 < Nat.card H := by
    rw [← hD]
    by_contra! hge
    exact hDH.ne (eq_of_le_of_card_ge hDH.le hge)
  have hdvd : p - 1 ∣ Nat.card H := hD ▸ card_dvd_of_le hDH.le
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
      (p := p) (f := 1) (by simpa using hF) H with
    hElem | hCyc | hDih | hA4 | hS4 | hA5 | hBorel | hPSL | hPGL
  · let : IsElementaryAbelian p H := hElem
    obtain ⟨m, hm⟩ := (IsElementaryAbelian.isPGroup p H).exists_card_eq
    rw [hm] at hdvd
    have hh := (hcop.pow_right m).eq_one_of_dvd hdvd
    omega
  · obtain ⟨z, hz, hc, _⟩ := hCyc
    rw [hgcd, hF] at hz
    rcases hz with hz | hz
    all_goals
      have hbound := Nat.le_of_dvd (by omega) hz
      omega
  · obtain ⟨z, hz, hc, _⟩ := hDih
    rw [hgcd, hF] at hz
    rcases hz with hz | hz
    · have hbound := Nat.le_of_dvd (by omega : 0 < (p - 1) / 2) hz
      omega
    · have hbound := Nat.le_of_dvd (by omega : 0 < (p + 1) / 2) hz
      have hd : p - 1 ∣ p + 1 := by
        have hq : 2 * ((p + 1) / 2) = p + 1 := by
          obtain ⟨k, hk⟩ := ho
          omega
        exact hdvd.trans (hc ▸ (hq ▸ Nat.mul_dvd_mul_left 2 hz))
      have hd2 : p - 1 ∣ 2 := by
        have heq : p + 1 = (p - 1) + 2 := by omega
        rw [heq] at hd
        exact (Nat.dvd_add_iff_right (dvd_refl (p - 1))).mpr hd
      have := Nat.le_of_dvd (by decide : 0 < 2) hd2
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
    let : IsSimpleGroup H := f.isSimpleGroup
    have hc : Nat.card H = 60 := by
      have hh := Nat.card_congr f.toEquiv
      rw [nat_card_alternatingGroup, Nat.card_fin] at hh
      norm_num at hh
      exact hh
    have hd30 : Nat.card D = 30 := by
      rw [hD]
      exact large_divisor_sixty (by omega) (by omega) (hc ▸ hdvd)
    let A := D.subgroupOf H
    have hA : Nat.card A = 30 :=
      (Nat.card_congr (subgroupOfEquivOfLe hDH.le).toEquiv).trans hd30
    have hindex : A.index = 2 := by
      have hh := A.card_mul_index
      rw [hA, hc] at hh
      omega
    rcases (A.normal_of_index_eq_two hindex).eq_bot_or_eq_top with hbot | htop
    · simp [hbot] at hA
    · have hh : Nat.card A = Nat.card H := by rw [htop]; simp
      omega
  · obtain ⟨m, t, _, ht, N, C, hN, _, hcN, _, hcC, hdisj, hsup⟩ := hBorel
    let : N.Normal := hN
    have hc : Nat.card H = p ^ m * t := by
      have hh := card_sup_eq_mul_of_normalizes_of_disjoint N C
        (by rw [N.normalizer_eq_top]; exact le_top) hdisj
      simpa [hsup, hcN, hcC] using hh
    rw [hc] at hdvd
    have hd := (hcop.pow_right m).dvd_of_dvd_mul_left hdvd
    have htpos : 0 < t := hcC ▸ Nat.card_pos (α := C)
    have hlow := Nat.le_of_dvd htpos hd
    have hgcd' : Nat.gcd (p - 1) 2 = 2 := by rwa [hF] at hgcd
    simp only [pow_one, hgcd'] at ht
    have hhigh := Nat.le_of_dvd (by omega : 0 < (p - 1) / 2) ht
    omega
  · obtain ⟨m, hm0, hmdiv, ⟨f⟩⟩ := hPSL
    have hm1 : m = 1 := Nat.dvd_one.mp hmdiv
    have hmcard := GaloisField.card p m hm0
    have hmOdd : Odd (Nat.card (GaloisField p m)) := hmcard ▸ ho.pow
    have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
      (F := GaloisField p m) hmOdd
    rw [hmcard, ← Nat.card_congr f.toEquiv, hm1, pow_one] at hc
    exact eq_top_of_card_eq H
      (Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2) (hc.trans hcard.symm))
  · obtain ⟨m, hm0, hmdiv, _⟩ := hPGL
    have hb := Nat.le_of_dvd (by decide : 0 < 1) hmdiv
    omega

/-- A torus normalizer of odd half-order is maximal for prime or quadratic fields. -/
theorem low_torus_isCoatom {F : Type*} [Field F] [Finite F]
    {p e : ℕ} [Fact p.Prime] (ho : Odd p) (he : e = 1 ∨ e = 2)
    (hF : Nat.card F = p ^ e) (hlarge : 25 < p ^ e)
    (D : Subgroup (PSL2MatrixGroup F))
    (hD : Nat.card D = Nat.card F - 1 ∨ Nat.card D = Nat.card F + 1)
    (hhalf : Odd (Nat.card D / 2)) : IsCoatom D := by
  rcases hD with hD | hD
  · have he1 : e = 1 := by
      rcases he with h | rfl
      · exact h
      · obtain ⟨k, hk⟩ := ho
        have hs : p ^ 2 = 4 * (k * k + k) + 1 := by nlinarith
        rw [hD, hF, hs] at hhalf
        obtain ⟨j, hj⟩ := hhalf
        omega
    subst e
    simp only [pow_one] at hF hlarge
    exact isCoatom_of_card_eq_prime_pred ho hF hlarge D (hD.trans (by rw [hF]))
  · exact Theory.PSL2.isCoatom_of_card_eq_field_succ ho he hF hlarge D
      (hD.trans (by rw [hF]))

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration.Diagonal
