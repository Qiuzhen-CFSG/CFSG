module
public import Theory.SpecificGroups.PSL2.PrimeNonsolvableSubgroups
public import Theory.SpecificGroups.PSL2.OuterSolvable.Models
public import GorensteinWalter.PGL2Cardinality
public import Mathlib.GroupTheory.IndexNormal

/-!
# Proper binary rank-one overgroups of half a Sylow

Every proper nonsolvable subgroup of PSL₂(2ⁿ) has index divisible by four.
Dickson's elementary, cyclic, dihedral, and affine alternatives are solvable.
For the subfield alternatives, the two-part of the index and divisibility of
field degrees force either the full group or the solvable field of order two.
The alternating-five alternative has two-part four and forces the full
PSL₂(4) model when the index is not divisible by four.

This is the model calculation for the half-Sylow local-persistence step in
Aschbacher–Smith 2.4.25, printed p.542. It uses the proved Dickson theorem
and the actual finite-field order formulas.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace Theory.PSL2

private theorem binary_order_factorization {n : ℕ} (hn : 0 < n) :
    (2^n * ((2^n)^2-1)).factorization 2 = n := by
  have hpos : 1 < 2^n := Nat.one_lt_pow hn.ne' (by decide)
  have hodd : Odd ((2^n)^2-1) := by
    have he : Even ((2^n)^2) := ((even_two.pow_of_ne_zero hn.ne').pow_of_ne_zero (by decide))
    exact Nat.Even.sub_odd (by nlinarith) he odd_one
  rw [Nat.factorization_mul (by positivity) (Nat.sub_pos_of_lt (by nlinarith : 1 < (2^n)^2)).ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat, add_zero]
  simp [Nat.prime_two.factorization_pow]

private theorem binary_card {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) :
    Nat.card (PSL2MatrixGroup F) = 2^n * ((2^n)^2-1) := by
  rw [← Nat.card_congr (sl2QuotientEquiv F).toEquiv,
    GorensteinWalter.sl2_card_formula, hF]

private theorem solvable_card_six {A : Type*} [_root_.Group A] [Finite A]
    (hA : Nat.card A = 6) : _root_.Group.IsSolvable A := by
  let P : Sylow 3 A := Sylow.nonempty.some
  have hP : Nat.card P = 3 := by
    have hf : Nat.factorization 6 3 = 1 := by
      change Nat.factorization (2*3) 3 = 1
      rw [Nat.factorization_mul (by decide) (by decide)]
      norm_num [Nat.prime_two.factorization,Nat.prime_three.factorization]
    rw [P.card_eq_multiplicity,hA,hf,pow_one]
  have hi : (P : Subgroup A).index = 2 := by
    have he := (P : Subgroup A).card_mul_index
    rw [hP,hA] at he
    omega
  let : (P : Subgroup A).Normal := normal_of_index_eq_two hi
  let : _root_.Group.IsNilpotent P := P.isPGroup'.isNilpotent
  have hpq : IsPGroup 2 (A ⧸ (P : Subgroup A)) :=
    IsPGroup.of_card (n := 1) (by simpa only [←index_eq_card,pow_one] using hi)
  let : _root_.Group.IsNilpotent (A ⧸ (P : Subgroup A)) :=
    hpq.isNilpotent
  exact _root_.Group.isSolvable_of_ker_le_range (P : Subgroup A).subtype
    (QuotientGroup.mk' (P : Subgroup A)) (by simp)

/-- Every proper nonsolvable subgroup of binary PSL₂ has index divisible by four. -/
theorem binary_four_dvd_index_of_nonsolvable
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (H : Subgroup (PSL2MatrixGroup F)) (hne : H ≠ ⊤)
    (hns : ¬ _root_.Group.IsSolvable H) : 4 ∣ H.index := by
  by_contra hi
  have hi' : H.index.factorization 2 ≤ 1 := by
    have hh := (Nat.prime_two.pow_dvd_iff_le_factorization
      (k := 2) H.index_ne_zero_of_finite).not.mp hi
    omega
  have hbound : n ≤ (Nat.card H).factorization 2 + 1 := by
    have he := congrArg (fun a : ℕ => a.factorization 2) H.card_mul_index
    rw [binary_card hF,binary_order_factorization hn,
      Nat.factorization_mul Nat.card_pos.ne' H.index_ne_zero_of_finite,Finsupp.add_apply] at he
    omega
  have degree_eq_or_small (m : ℕ) (hm : m ≠ 0) (hd : m ∣ n)
      (hcard : Nat.card H = 2^m*((2^m)^2-1)) : m = n ∨ m = 1 := by
    rw [hcard,binary_order_factorization (by omega)] at hbound
    have hmle := Nat.le_of_dvd hn hd
    by_cases he : m = n
    · exact .inl he
    right
    obtain ⟨k,hk⟩ := hd
    have hk2 : 2 ≤ k := by
      by_contra hh
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl <;> simp_all
    nlinarith
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hF H with
    hEl | hCyc | hDih | hA4 | hS4 | hA5 | hAff | hPSL | hPGL
  · let := hEl
    exact hns inferInstance
  · obtain ⟨z,_,_,hc⟩ := hCyc
    let := hc
    exact hns inferInstance
  · obtain ⟨z,_,_,⟨e⟩⟩ := hDih
    let := GLS3.Chapter5.dihedralGroup_isSolvable z
    exact hns (_root_.Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  · obtain ⟨e⟩ := hA4.2
    let := Equiv.Perm.isSolvable_fin_four
    exact hns (_root_.Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  · obtain ⟨e⟩ := hS4.2
    let := Equiv.Perm.isSolvable_fin_four
    exact hns (_root_.Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  · obtain ⟨e⟩ := hA5.2
    have hc : Nat.card H = 60 := by
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [hc] at hbound
    have hf60 : Nat.factorization 60 2 = 2 := by
      rw [show 60 = 2^2*15 by decide,Nat.factorization_mul (by decide) (by decide)]
      rw [Finsupp.add_apply,Nat.prime_two.factorization_pow,
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 15)]
      simp
    rw [hf60] at hbound
    have hn2 : n = 2 := by
      have hd := hA5.1.resolve_left (by decide)
      interval_cases n <;> norm_num at hd
      rfl
    exact hne (H.eq_top_of_card_eq (by rw [hc,binary_card hF,hn2]; norm_num))
  · obtain ⟨m,t,_,_,N,C,hN,hNe,_,hC,_,_,hg⟩ := hAff
    let := hN
    let := hNe
    let := hC
    exact hns (_root_.Group.isSolvable_of_normal_sup_eq_top N C hg)
  · obtain ⟨m,hm,hd,⟨e⟩⟩ := hPSL
    have hc : Nat.card H = 2^m*((2^m)^2-1) := by
      rw [Nat.card_congr e.toEquiv,binary_card (GaloisField.card 2 m hm)]
    rcases degree_eq_or_small m hm hd hc with he | he
    · exact hne (H.eq_top_of_card_eq (by rw [hc,binary_card hF,he]))
    · exact hns (solvable_card_six (by rw [hc,he]; norm_num))
  · obtain ⟨m,hm,hd,⟨e⟩⟩ := hPGL
    have hc : Nat.card H = 2^m*((2^m)^2-1) := by
      rw [Nat.card_congr e.toEquiv,GorensteinWalter.pgl2_card_formula,
        GaloisField.card 2 m hm]
    rcases degree_eq_or_small m hm ((dvd_mul_left m 2).trans hd) hc with he | he
    · have hh := Nat.le_of_dvd hn hd
      omega
    · exact hns (solvable_card_six (by rw [hc,he]; norm_num))
end Theory.PSL2
