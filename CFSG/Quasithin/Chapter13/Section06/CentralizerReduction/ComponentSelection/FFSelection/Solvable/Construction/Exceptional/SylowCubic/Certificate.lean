module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.SylowCubic.Finite
public import Mathlib.GroupTheory.Complement
/-!
# Sylow transport and the order-nine obstruction

Conjugacy transports the canonical six-word certificate to every Sylow
two-subgroup of the literal parity actor. The resulting two commuting cubics
have distinct cyclic subgroups and therefore generate a subgroup of order nine.
Both elements lie in the Sylow-conjugate closure of the original cubic.

This proves the finite input consumed by `eq_cubic_of_closure_restriction`;
no normality or subnormality of the subgroup under investigation is assumed.
Source motivation: Aschbacher–Smith, B.5.6(4), B.5.7 and 13.6.13,
printed pp.105–106 and 929.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SixPoint

private lemma zpow_cases {G : Type*} [Group G] [Finite G] (a : G)
    (ha : orderOf a = 3) {x : G} (hx : x ∈ zpowers a) :
    x = 1 ∨ x = a ∨ x = a ^ 2 := by
  classical
  rw [isOfFinOrder_of_finite a |>.mem_zpowers_iff_mem_range_orderOf] at hx
  simp only [ha, Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  interval_cases i <;> simp


private lemma sq_eq_to_sq {G : Type*} [Group G] (u v : G) (hu : u ^ 3 = 1)
    (h : u ^ 2 = v) : u = v ^ 2 := by
  calc
    u = u ^ 4 := by rw [show 4 = 3 + 1 by norm_num, pow_add, hu, one_mul]; simp
    _ = (u ^ 2) ^ 2 := by rw [← pow_mul]
    _ = v ^ 2 := by rw [h]

private lemma sq_eq_sq_to_eq {G : Type*} [Group G] (u v : G)
    (hu : u ^ 3 = 1) (hv : v ^ 3 = 1) (h : u ^ 2 = v ^ 2) : u = v := by
  calc
    u = u ^ 4 := by rw [show 4 = 3 + 1 by norm_num, pow_add, hu, one_mul]; simp
    _ = (u ^ 2) ^ 2 := by rw [← pow_mul]
    _ = (v ^ 2) ^ 2 := by rw [h]
    _ = v ^ 4 := by rw [← pow_mul]
    _ = v := by rw [show 4 = 3 + 1 by norm_num, pow_add, hv, one_mul]; simp

private lemma card_sup_zpowers_of_three {G : Type*} [Group G] [Finite G]
    (a b : G) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (hcomm : a * b = b * a)
    (hneq : b ≠ a) (hneq2 : b ≠ a ^ 2) :
    Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) = 9 := by
  classical
  have hoa : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hob : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hca : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, hoa]
  have hcb : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hob]
  have hdis : Disjoint (Subgroup.zpowers a) (Subgroup.zpowers b) := by
    rw [disjoint_iff_inf_le]
    intro x hx
    have hxa := zpow_cases a hoa hx.1
    have hxb := zpow_cases b hob hx.2
    rcases hxa with hx1 | hxa | hxa <;>
      rcases hxb with hy1 | hxb | hxb <;>
      simp_all [pow_two]
    all_goals
      first
      | exfalso
        apply hneq2
        have hh := sq_eq_to_sq b a hb3 (by simpa [pow_two] using hxa)
        simpa [pow_two] using hh
      | exfalso
        apply hneq
        have hh := sq_eq_sq_to_eq b a hb3 ha3 (by simpa [pow_two] using hxa)
        exact hh
  let S : Subgroup G := Subgroup.zpowers a ⊔ Subgroup.zpowers b
  let A : Subgroup S := (Subgroup.zpowers a).subgroupOf S
  let B : Subgroup S := (Subgroup.zpowers b).subgroupOf S
  have hAcard : Nat.card A = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv, hca]
  have hBcard : Nat.card B = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv, hcb]
  have hcentral : A ≤ Subgroup.centralizer (B : Set S) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    change (x : G) ∈ Subgroup.zpowers a at hx
    change (y : G) ∈ Subgroup.zpowers b at hy
    rcases Subgroup.mem_zpowers_iff.mp hy with ⟨m, hm⟩
    rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, hn⟩
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hn, ← hm]
    exact (Commute.zpow_zpow (show Commute a b from hcomm) n m).eq.symm
  have hnorm : A ≤ Subgroup.normalizer (B : Set S) :=
    hcentral.trans (Subgroup.centralizer_le_normalizer _)
  have htop : A ⊔ B = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    simp [S]
  have hdis' : Disjoint A B := by
    rw [disjoint_iff_inf_le]
    intro x hx
    apply Subtype.ext
    apply hdis.le_bot
    exact ⟨show (x : G) ∈ Subgroup.zpowers a from hx.1,
      show (x : G) ∈ Subgroup.zpowers b from hx.2⟩
  have hmul : (↑A : Set S) * (↑B : Set S) = Set.univ := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right A B hnorm]
    exact congrArg (fun H : Subgroup S => (H : Set S)) htop
  have hcomp : A.IsComplement' B := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis' hmul
  rw [← hcomp.card_mul_card, hAcard, hBcard]

/-- Every Sylow subgroup supplies a commuting conjugate outside the seed's cubic. -/
theorem commuting_conjugate (P : Sylow 2 Actor) (r : Actor) (hthree : r ^ 3 = 1)
    (hfirst : firstProjection r ≠ 1) (hsecond : secondProjection r ≠ 1) :
    ∃ p ∈ P, r * (p * r * p⁻¹) = (p * r * p⁻¹) * r ∧
      p * r * p⁻¹ ≠ r ∧ p * r * p⁻¹ ≠ r ^ 2 := by
  obtain ⟨P₀, hP₀⟩ := SylowCubicCertificate.exists_sylow_commuting_conjugates
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Actor P₀ P
  let e : Actor ≃* Actor := MulAut.conj g
  let s := e.symm r
  have hes : e s = r := e.apply_symm_apply r
  have hs : s ^ 3 = 1 := by
    dsimp [s]
    rw [← map_pow, hthree, map_one]
  have hsf : firstProjection s ≠ 1 := by
    intro h
    apply hfirst
    rw [← hes]
    change firstProjection (g * s * g⁻¹) = 1
    simp only [map_mul, map_inv, h, mul_one, mul_inv_cancel]
  have hss : secondProjection s ≠ 1 := by
    intro h
    apply hsecond
    rw [← hes]
    change secondProjection (g * s * g⁻¹) = 1
    simp only [map_mul, map_inv, h, mul_one, mul_inv_cancel]
  obtain ⟨p, hp, hc, hn, hn2⟩ :=
    hP₀ s hs hsf hss
  have hep : e p ∈ P := by
    rw [← hg]
    exact Subgroup.smul_mem_pointwise_smul p (MulAut.conj g)
      (P₀ : Subgroup Actor) hp
  have hec : e (p * s * p⁻¹) = e p * r * (e p)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hes]
  refine ⟨e p, hep, ?_, ?_, ?_⟩
  · simpa only [map_mul, hes, hec] using congrArg e hc
  · intro h
    apply hn
    apply e.injective
    rw [hec, hes]
    exact h
  · intro h
    apply hn2
    apply e.injective
    rw [hec, map_pow, hes]
    exact h

/-- A noncanonical cubic has Sylow-conjugate closure of order divisible by nine. -/
theorem closure_restriction (P : Sylow 2 Actor) (r : Actor) (hthree : r ^ 3 = 1)
    (hsecond : secondProjection r ≠ 1) :
    firstProjection r = 1 ∨ 9 ∣ Nat.card (sylowConjugateClosure P r) := by
  classical
  by_cases hf : firstProjection r = 1
  · exact Or.inl hf
  obtain ⟨p, hp, hc, hn, hn2⟩ := commuting_conjugate P r hthree hf hsecond
  let b := p * r * p⁻¹
  have hr1 : r ≠ 1 := by intro h; exact hsecond (by rw [h, map_one])
  have hb3 : b ^ 3 = 1 := by
    change (MulAut.conj p r) ^ 3 = 1
    rw [← map_pow, hthree, map_one]
  have hb1 : b ≠ 1 := by
    intro h
    apply hr1
    exact (MulAut.conj p).injective (h.trans (map_one _).symm)
  have hcard : Nat.card ↥(zpowers r ⊔ zpowers b) = 9 :=
    card_sup_zpowers_of_three r b hthree hr1 hb3 hb1 hc hn hn2
  have hle : zpowers r ⊔ zpowers b ≤ sylowConjugateClosure P r := by
    apply sup_le
    · apply zpowers_le.mpr
      exact Subgroup.subset_closure ⟨1, (P : Subgroup Actor).one_mem, by simp⟩
    · apply zpowers_le.mpr
      exact Subgroup.subset_closure ⟨p, hp, rfl⟩
  exact Or.inr (hcard ▸ card_dvd_of_le hle)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SixPoint
