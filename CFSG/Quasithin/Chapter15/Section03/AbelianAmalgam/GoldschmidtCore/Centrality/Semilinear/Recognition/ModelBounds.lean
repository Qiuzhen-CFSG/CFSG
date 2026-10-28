module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.LinearTwoSylow
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.LinearThreeBound
public import GorensteinWalter.PSL2DihedralSylow
public import GorensteinWalter.PSL2Cardinality

/-!
# Concrete order and Sylow comparisons for the F.6.18 models

An elementary dihedral Sylow has order four, so an actual odd PSL₂ model
which is also a binary SL₂ model is identified with A₅ through the binary
field isomorphism. Odd degree-three models contain a defining-prime cube
in their group order. None of the binary rank-one groups whose Sylow order
is at most 128 has such an odd-prime cube divisor: seven small integer
factorizations prove this without enumerating matrix-group elements.

All comparisons act on supplied model isomorphisms. No group is recognized
by its order. The universal source classification is used only by the
separate exhaustive comparison.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, F.6.18,
pp.309--310, and B.5.1/B.5.6, in the repaired 15.3.68 comparison.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open FSource
universe u
variable {D : Type u} [Group D] [Finite D]

omit [Finite D] in
/-- Cardinality of the source extension from its genuine kernel and quotient. -/
theorem extension_card {A B : Type*} [Group A] [Group B]
    (h : Extension D A B) : Nat.card D = Nat.card A * Nat.card B := by
  obtain ⟨N, hN, ⟨a⟩, ⟨b⟩⟩ := h
  let : N.Normal := hN
  rw [← Nat.card_congr a.toEquiv, ← Nat.card_congr b.toEquiv,
    ← Subgroup.index_eq_card, Subgroup.card_mul_index]

/-- Every section isomorphic to a symmetric group of degree at least six
contains the explicit alternating cubic plane. -/
theorem no_symmetric_section (hr : primeRank 3 D ≤ 1) (A : Subgroup D)
    {n : ℕ} (hn : 6 ≤ n) (q : A →* Equiv.Perm (Fin n))
    (hq : Function.Surjective q) : False := by
  have hu := three_rank_section hr A q hq
  have hl := alternatingGroup.TwoThreeCycles.two_le_primeRank hn
  have hh := (primeRank_le_of_injective 3
    (alternatingGroup (Fin n)).subtype Subtype.val_injective).trans hu
  omega

/-- Any Sylow inside a subgroup has order bounded by an ambient Sylow. -/
theorem subgroup_sylow_card_le (A : Subgroup D) (P : Sylow 2 A) (S : Sylow 2 D) :
    Nat.card P ≤ Nat.card S := by
  obtain ⟨R, hR⟩ := (P.isPGroup'.map A.subtype).exists_le_sylow
  have h := (card_le_of_le hR).trans (Nat.card_congr (R.equiv S).toEquiv).le
  rwa [card_map_of_injective A.subtype_injective] at h

/-- The small ambient Sylow bound bounds a binary rank-one field degree. -/
theorem linearTwo_degree_le_seven (A : Subgroup D) (F : BinaryField)
    (e : A ≃* SL(2,F.Carrier)) (S : Sylow 2 D) (hS : Nat.card S ≤ 128) :
    F.degree ≤ 7 := by
  let P : Sylow 2 A := Classical.choice inferInstance
  let R := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hr : Nat.card R = Nat.card P := card_map_of_injective e.injective
  have hb : 2 ^ F.degree ≤ 2 ^ 7 := by
    rw [← linearTwo_sylow_card F R, hr]
    exact (subgroup_sylow_card_le A P S).trans hS
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb

/-- An elementary dihedral two-group has order four. -/
theorem elementary_dihedral_sylow_card_four
    {A : Type*} [Group A] [Finite A] (P : Sylow 2 A)
    (he : IsElementaryAbelian 2 P) {n : ℕ} (hn : 1 ≤ n)
    (e : P ≃* DihedralGroup (2 ^ n)) : Nat.card P = 4 := by
  let : IsElementaryAbelian 2 P := he
  have hx : (e.symm (DihedralGroup.r 1)) ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 P) _
  have hd : 2 ^ n ∣ 2 := by
    have h := congrArg e hx
    rw [map_pow, MulEquiv.apply_symm_apply, map_one] at h
    simpa only [DihedralGroup.orderOf_r_one] using orderOf_dvd_of_pow_eq_one h
  have hp : 2 ^ n ≤ 2 ^ 1 := Nat.le_of_dvd (by decide) hd
  have hn' : n ≤ 1 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, show n = 1 by omega]
  norm_num

/-- Comparing actual odd and binary PSL₂ models gives A₅ through the
binary field equivalence, since the common Sylow is elementary dihedral. -/
theorem odd_linearTwo_binary_alternatingFive (F : BinaryField)
    {K : Type*} [Field K] [Finite K]
    (hK : GorensteinWalter.IsOddPrimePower (Nat.card K))
    (e : D ≃* SL(2,F.Carrier)) (a : D ≃* PSL(2,K)) :
    Nonempty (D ≃* alternatingGroup (Fin 5)) := by
  let P : Sylow 2 D := Classical.choice inferInstance
  let R := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let Q := P.mapSurjective (f := a.toMonoidHom) a.surjective
  let er : P ≃* R := e.subgroupMap _
  let eq : P ≃* Q := a.subgroupMap _
  have he : IsElementaryAbelian 2 P := by
    let : IsElementaryAbelian 2 R := linearTwo_sylow_elementary F R
    refine {
      toIsMulCommutative := ⟨⟨fun x y => er.injective ?_⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => er.injective ?_ }
    · simp only [map_mul, mul_comm]
    · rw [map_pow, map_one]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 R) _
  obtain ⟨n, hn, ⟨em⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model K hK Q
  exact (linearTwo_alternatingFive_of_sylow_four F e P
    (elementary_dihedral_sylow_card_four P he hn (eq.trans em))).2

omit [Finite D] in
/-- The defining-prime cube in every special or projective degree-three model. -/
theorem degreeThree_prime_cube {p : ℕ} (hp : p.Prime) (h : DegreeThree p D) :
    p ^ 3 ∣ Nat.card D := by
  cases h with
  | linear F hc _ e =>
    rw [Nat.card_congr e.toEquiv]
    have h := Matrix.ProjectiveSpecialLinearGroup.psl3_cube_dvd_card (F := F)
    rw [hc] at h
    exact h.trans (Subgroup.card_dvd_of_surjective (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective (center SL(3,F))))
  | projectiveLinear F hc _ e =>
    rw [Nat.card_congr e.toEquiv, ← hc]
    exact Matrix.ProjectiveSpecialLinearGroup.psl3_cube_dvd_card
  | unitary F J hc hf _ e =>
    rw [Nat.card_congr e.toEquiv]
    exact J.prime_cube_dvd_card_special hp hc hf
  | projectiveUnitary F J hc hf _ e =>
    rw [Nat.card_congr e.toEquiv]
    exact J.prime_cube_dvd_card_projective hp hc hf


private theorem no_odd_prime_cube_6 {p : ℕ} (hp : p.Prime) (hne : p ≠ 2)
    (h : p ^ 3 ∣ 6) : False := by
  have hd : p ∣ 2 * 3 := (dvd_pow_self p (by decide : 3 ≠ 0)).trans h
  have he : p = 2 ∨ p = 3 := by
    simpa only [hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3), or_assoc] using hd
  rcases he with rfl | rfl
  all_goals first | exact hne rfl | norm_num at h

private theorem no_odd_prime_cube_60 {p : ℕ} (hp : p.Prime) (hne : p ≠ 2)
    (h : p ^ 3 ∣ 60) : False := by
  have hd : p ∣ 2 * 2 * 3 * 5 := (dvd_pow_self p (by decide : 3 ≠ 0)).trans h
  have he : p = 2 ∨ p = 2 ∨ p = 3 ∨ p = 5 := by
    simpa only [hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5), or_assoc] using hd
  rcases he with rfl | rfl | rfl | rfl
  all_goals first | exact hne rfl | norm_num at h

private theorem no_odd_prime_cube_168 {p : ℕ} (hp : p.Prime) (hne : p ≠ 2)
    (h : p ^ 3 ∣ 168) : False := by
  have hd : p ∣ 2 * 2 * 2 * 3 * 7 := (dvd_pow_self p (by decide : 3 ≠ 0)).trans h
  have he : p = 2 ∨ p = 2 ∨ p = 2 ∨ p = 3 ∨ p = 7 := by
    simpa only [hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7), or_assoc] using hd
  rcases he with rfl | rfl | rfl | rfl | rfl
  all_goals first | exact hne rfl | norm_num at h

private theorem no_odd_prime_cube_504 {p : ℕ} (hp : p.Prime) (hne : p ≠ 2)
    (h : p ^ 3 ∣ 504) : False := by
  have hd : p ∣ 2 * 2 * 2 * 3 * 3 * 7 := (dvd_pow_self p (by decide : 3 ≠ 0)).trans h
  have he : p = 2 ∨ p = 2 ∨ p = 2 ∨ p = 3 ∨ p = 3 ∨ p = 7 := by
    simpa only [hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7), or_assoc] using hd
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact hne rfl | norm_num at h

private theorem no_odd_prime_cube_4080 {p : ℕ} (hp : p.Prime) (hne : p ≠ 2)
    (h : p ^ 3 ∣ 4080) : False := by
  have hd : p ∣ 2 * 2 * 2 * 2 * 3 * 5 * 17 := (dvd_pow_self p (by decide : 3 ≠ 0)).trans h
  have he : p = 2 ∨ p = 2 ∨ p = 2 ∨ p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 17 := by
    simpa only [hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 17), or_assoc] using hd
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact hne rfl | norm_num at h

private theorem no_odd_prime_cube_32736 {p : ℕ} (hp : p.Prime) (hne : p ≠ 2)
    (h : p ^ 3 ∣ 32736) : False := by
  have hd : p ∣ 2 * 2 * 2 * 2 * 2 * 3 * 11 * 31 := (dvd_pow_self p (by decide : 3 ≠ 0)).trans h
  have he : p = 2 ∨ p = 2 ∨ p = 2 ∨ p = 2 ∨ p = 2 ∨ p = 3 ∨ p = 11 ∨ p = 31 := by
    simpa only [hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 31), or_assoc] using hd
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact hne rfl | norm_num at h

private theorem no_odd_prime_cube_262080 {p : ℕ} (hp : p.Prime) (hne : p ≠ 2)
    (h : p ^ 3 ∣ 262080) : False := by
  have hd : p ∣ 2 * 2 * 2 * 2 * 2 * 2 * 3 * 3 * 5 * 7 * 13 := (dvd_pow_self p (by decide : 3 ≠ 0)).trans h
  have he : p = 2 ∨ p = 2 ∨ p = 2 ∨ p = 2 ∨ p = 2 ∨ p = 2 ∨ p = 3 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13 := by
    simpa only [hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 13), or_assoc] using hd
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact hne rfl | norm_num at h

private theorem no_odd_prime_cube_2097024 {p : ℕ} (hp : p.Prime) (hne : p ≠ 2)
    (h : p ^ 3 ∣ 2097024) : False := by
  have hd : p ∣ 2 * 2 * 2 * 2 * 2 * 2 * 2 * 3 * 43 * 127 := (dvd_pow_self p (by decide : 3 ≠ 0)).trans h
  have he : p = 2 ∨ p = 2 ∨ p = 2 ∨ p = 2 ∨ p = 2 ∨ p = 2 ∨ p = 2 ∨ p = 3 ∨ p = 43 ∨ p = 127 := by
    simpa only [hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 43),
      Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 127), or_assoc] using hd
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact hne rfl | norm_num at h

/-- No defining odd-prime cube divides any binary rank-one model allowed
by the ambient Sylow bound. The eight small factorizations are checked
arithmetically, without enumerating elements of any matrix group. -/
theorem linearTwo_no_odd_prime_cube (F : BinaryField) (hn : F.degree ≤ 7)
    {p : ℕ} (hp : p.Prime) (hne : p ≠ 2) : ¬ p ^ 3 ∣ Nat.card SL(2,F.Carrier) := by
  intro h
  rw [GorensteinWalter.sl2_card_formula, F.card_eq] at h
  have hlo := F.degree_pos
  generalize hk : F.degree = k at h hn hlo
  interval_cases k
  · exact no_odd_prime_cube_6 hp hne h
  · exact no_odd_prime_cube_60 hp hne h
  · exact no_odd_prime_cube_504 hp hne h
  · exact no_odd_prime_cube_4080 hp hne h
  · exact no_odd_prime_cube_32736 hp hne h
  · exact no_odd_prime_cube_262080 hp hne h
  · exact no_odd_prime_cube_2097024 hp hne h

omit [Finite D] in
/-- The degree-three odd models cannot be the actual binary three-space
actor, by defining-prime divisibility and the order 168. -/
theorem degreeThree_not_binaryThree {p : ℕ} (hp : p.Prime) (hne : p ≠ 2)
    (h : DegreeThree p D) (e : D ≃* SL(3,ZMod 2)) : False := by
  have hd := degreeThree_prime_cube hp h
  rw [Nat.card_congr e.toEquiv, Matrix.PSL3Two.card_SL] at hd
  exact no_odd_prime_cube_168 hp hne hd

omit [Finite D] in
/-- The A₅ component is excluded by the same intrinsic order divisor. -/
theorem degreeThree_not_alternatingFive {p : ℕ} (hp : p.Prime) (hne : p ≠ 2)
    (h : DegreeThree p D) (e : D ≃* alternatingGroup (Fin 5)) : False := by
  have hd := degreeThree_prime_cube hp h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at hd
  exact no_odd_prime_cube_60 hp hne (by simpa [Nat.factorial] using hd)

/-- Odd PSL₂ has a cubic element; in the product row it is independent
of the separately embedded C₃. -/
theorem three_dvd_odd_pslTwo {F : Type*} [Field F] [Finite F]
    (ho : Odd (Nat.card F)) : 3 ∣ Nat.card PSL(2,F) := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hq2 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hm : Nat.card F % 3 = 0 ∨ Nat.card F % 3 = 1 ∨ Nat.card F % 3 = 2 := by omega
  have hd : 3 ∣ Nat.card F * (Nat.card F ^ 2 - 1) := by
    rcases hm with hm | hm | hm
    · exact dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero hm) _
    · have he : Nat.card F ^ 2 % 3 = 1 := by norm_num [Nat.pow_mod, hm]
      exact dvd_mul_of_dvd_right (show 3 ∣ Nat.card F ^ 2 - 1 from by omega) _
    · have he : Nat.card F ^ 2 % 3 = 1 := by norm_num [Nat.pow_mod, hm]
      exact dvd_mul_of_dvd_right (show 3 ∣ Nat.card F ^ 2 - 1 from by omega) _
  rw [← Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice ho] at hd
  exact (Nat.Coprime.symm (by decide : Nat.Coprime 2 3)).dvd_of_dvd_mul_right hd
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
