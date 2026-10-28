module

public import Glauberman.DicksonClassification
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import GorensteinWalter.PGL2Cardinality
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Tactic

/-!
# Maximal subgroups of order q+1 in prime and quadratic PSL2 groups

For q = p or p², odd and greater than 25, every subgroup of order q+1
is maximal. Dickson's classification reduces an overgroup to order
comparisons. The Borel alternatives are excluded by coprimality with p;
the proper subfield alternatives would force p²+1 to divide p(p²-1).
The only remaining exceptional overgroup would have order 60 and contain
an index-two subgroup of order 30, contrary to simplicity of A5.

The consumer in ThreeInvolutionGeneration applies this to the actual
nonsplit torus normalizer. No cyclicity or dihedral identification is
needed for this maximality criterion.

Sources: Huppert II.8.27 (Dickson), and Guralnick--Malle, Classification of
2F-modules I, Proposition 4.1, manuscript pp.8--9.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups
namespace Theory.PSL2

private theorem succ_power_coprime {p e : ℕ} (he : e ≠ 0) :
    (p ^ e + 1).Coprime p := by
  have hc : (p ^ e + 1).Coprime (p ^ e) :=
    Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _)
  exact hc.of_dvd_right (dvd_pow_self p he)

private theorem square_succ_not_dvd {p : ℕ} (hp : 2 ≤ p) :
    ¬ p ^ 2 + 1 ∣ p * (p ^ 2 - 1) := by
  intro hd
  have hd' := (succ_power_coprime (p := p) (e := 2) (by decide)).dvd_of_dvd_mul_left hd
  have hs : 4 ≤ p ^ 2 := by nlinarith
  have hpos : 0 < p ^ 2 - 1 := by omega
  have hh := Nat.le_of_dvd hpos hd'
  omega

private theorem thirty_of_large_divisor {n : ℕ} (hl : 26 < n) (hu : n < 60)
    (hd : n ∣ 60) : n = 30 := by
  interval_cases n <;> norm_num at *

/-- In odd prime or quadratic PSL2(q), q > 25, a subgroup of order q+1 is maximal. -/
theorem isCoatom_of_card_eq_field_succ {F : Type*} [Field F] [Finite F]
    {p e : ℕ} [Fact p.Prime] (ho : Odd p) (he : e = 1 ∨ e = 2)
    (hF : Nat.card F = p ^ e) (hlarge : 25 < p ^ e)
    (D : Subgroup (PSL2MatrixGroup F)) (hD : Nat.card D = p ^ e + 1) :
    IsCoatom D := by
  classical
  have he0 : e ≠ 0 := by omega
  have hp : p.Prime := Fact.out
  have hqodd : Odd (Nat.card F) := hF ▸ ho.pow
  have hcard := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) hqodd
  rw [hF] at hcard
  have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 := by
    apply Nat.gcd_eq_right_iff_dvd.mpr
    obtain ⟨k, hk⟩ := hqodd
    exact ⟨k, by omega⟩
  have hcop : (p ^ e + 1).Coprime p := succ_power_coprime he0
  have hDne : D ≠ ⊤ := by
    intro ht
    have hc : Nat.card (PSL2MatrixGroup F) = p ^ e + 1 := by
      simpa [ht] using hD
    rw [hc] at hcard
    have hsq : 5 ≤ (p ^ e) ^ 2 := by nlinarith
    have hs : 4 ≤ (p ^ e) ^ 2 - 1 := by omega
    have hb := Nat.mul_le_mul_left (p ^ e) hs
    nlinarith
  refine ⟨hDne, ?_⟩
  intro H hDH
  have hlt : p ^ e + 1 < Nat.card H := by
    rw [← hD]
    by_contra! hge
    exact hDH.ne (eq_of_le_of_card_ge hDH.le hge)
  have hdvd : p ^ e + 1 ∣ Nat.card H := hD ▸ card_dvd_of_le hDH.le
  have heq (hc : Nat.card H = Nat.card (PSL2MatrixGroup F)) : H = ⊤ :=
    eq_top_of_card_eq H hc
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hF H with
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
      have hpos : 0 < z := hc ▸ Nat.card_pos (α := H)
      have hbound := Nat.le_of_dvd (by omega) hz
      omega
  · obtain ⟨z, hz, hc, _⟩ := hDih
    rw [hgcd, hF] at hz
    rcases hz with hz | hz
    all_goals
      have hbound := Nat.le_of_dvd (by omega) hz
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
      exact thirty_of_large_divisor (by omega) (by omega) (hc ▸ hdvd)
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
    have hgcd' : Nat.gcd (p ^ e - 1) 2 = 2 := by rwa [hF] at hgcd
    rw [hgcd'] at ht
    have hhigh := Nat.le_of_dvd (by omega : 0 < (p ^ e - 1) / 2) ht
    omega
  · obtain ⟨m, hm0, hmdiv, ⟨f⟩⟩ := hPSL
    have hmcard := GaloisField.card p m hm0
    have hmOdd : Odd (Nat.card (GaloisField p m)) := hmcard ▸ ho.pow
    have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
      (F := GaloisField p m) hmOdd
    rw [hmcard, ← Nat.card_congr f.toEquiv] at hc
    by_cases hme : m = e
    · apply heq
      rw [hme] at hc
      exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2) (hc.trans hcard.symm)
    · have he2 : e = 2 := by
        rcases he with rfl | he
        · have := Nat.dvd_one.mp hmdiv
          omega
        · exact he
      have hm1 : m = 1 := by
        rw [he2] at hmdiv
        have := (Nat.dvd_prime Nat.prime_two).mp hmdiv
        omega
      have hd := hdvd.trans (dvd_mul_right (Nat.card H) 2)
      rw [hc, hm1, pow_one, he2] at hd
      exact (square_succ_not_dvd hp.two_le hd).elim
  · obtain ⟨m, hm0, hmdiv, ⟨f⟩⟩ := hPGL
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hbound := Nat.le_of_dvd (by omega : 0 < e) hmdiv
    have he2 : e = 2 := by omega
    have hm1 : m = 1 := by omega
    have hc := GorensteinWalter.pgl2_card_formula (GaloisField p m)
    rw [GaloisField.card p m hm0, ← Nat.card_congr f.toEquiv, hm1, pow_one] at hc
    rw [hc, he2] at hdvd
    exact (square_succ_not_dvd hp.two_le hdvd).elim

end Theory.PSL2
