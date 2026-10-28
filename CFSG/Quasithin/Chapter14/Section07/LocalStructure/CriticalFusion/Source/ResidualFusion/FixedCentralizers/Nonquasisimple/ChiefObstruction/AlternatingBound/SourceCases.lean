module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder


/-!
# The module bound in the A₇ specialization of C.2.7

Retain all eight alternatives of the full C.2.7 conclusion. The alternating,
exceptional A₇, A-hat₆ and G₂ block modules have order at most 64 directly
from their actual module identifications. In the rank-one field case, the
field order divides 2520, so its binary degree is at most three. The
symplectic four-space model is excluded by its matrix-group order.

For the two non-block rows, the literal map from the core quotient to the
star image has central kernel by C.2.7(1). The actual A₇ marking makes this
kernel trivial. Matrix-group order formulas then exclude the SL₃ and binary
PSL₄/PSL₅ star images. Thus no identification of the two quotients is assumed.
Both the ordinary six-dimensional and exceptional four-dimensional A₇ block
possibilities are retained. This result supplies the module bound consumed
by `Data.every_complete_K_chief_count_le_one_of_c27`.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), C.1.7,
C.1.12, C.1.22 and C.2.7, printed pp.123--124, 129, 145--147, applied in
14.7.68(2), printed pp.1071--1072.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.AlternatingBound
open ChapterC
open Chapter1.RadicalExclusions.ModelReduction
open FullSieve.SourceInterface

private theorem exponent_le_three {n : ℕ} (h : 2 ^ n ∣ 2520) : n ≤ 3 := by
  have hc : Nat.Coprime (2 ^ n) 315 := (by decide : Nat.Coprime 2 315).pow_left n
  have hd : 2 ^ n ∣ 2 ^ 3 := hc.dvd_mul_right.mp h
  exact (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp hd

private theorem sl_three_card (F : Type*) [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  let q := Nat.card F
  have hq : 1 < q := Finite.one_lt_card
  have h : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) * (q - 1) =
      ∏ i : Fin 3, (q ^ 3 - q ^ (i : ℕ)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (center (Matrix.SpecialLinearGroup (Fin 3) F)),
      Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
    exact Atlas.ExceptionalSupport.card_psl_mul 3
  simp only [Fin.prod_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one] at h
  have h1 : q ^ 3 - q = q * (q ^ 2 - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
    ring
  have h2 : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
  rw [h1, h2] at h
  apply Nat.eq_of_mul_eq_mul_right (show 0 < q - 1 by omega)
  rw [h]
  ring

private theorem not_sl_three_card (F : Type*) [Field F] [Finite F]
    {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) ≠ 2520 := by
  intro hc
  have hd : 2 ^ (n * 3) ∣ 2520 := by
    rw [← hc, sl_three_card, hF, pow_mul]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have hn1 : n = 1 := by have := exponent_le_three hd; omega
  rw [sl_three_card, hF, hn1] at hc
  norm_num at hc

private theorem alternating_module_card_le {E : Type*} [Group E]
    {n : ℕ} (hl : 5 ≤ n) (hu : n ≤ 8) (h : IsAlternatingBlock E n) :
    Nat.card (BlockModule E) ≤ 2 ^ 6 := by
  interval_cases n
  · rw [h.module_card_odd (by decide)]
    norm_num
  · rw [h.module_card_even (by decide)]
    norm_num
  · rw [h.module_card_odd (by decide)]
  · rw [h.module_card_even (by decide)]

private theorem binary_module_card_le {E : Type*} [Group E]
    (hc : Nat.card (E ⧸ pCore 2 E) = 2520)
    {n : ℕ} (h : IsL2EvenBlock E n) : Nat.card (BlockModule E) ≤ 2 ^ 6 := by
  obtain ⟨_, _, F, _, _, hF, _, hm⟩ := h
  have hsl : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 2520 :=
    (Nat.card_congr hm.quotient_iso.some.toEquiv).symm.trans hc
  have hd : 2 ^ n ∣ 2520 := by
    rw [← hsl, Atlas.card_sl_two, hF]
    exact dvd_mul_right _ _
  have hn := exponent_le_three hd
  rw [hm.module_card, Nat.card_fun, hF, Nat.card_fin, ← pow_mul]
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-- The actual core-to-star map is an isomorphism in the A7 case: C.2.7
makes its kernel central and the marked alternating quotient has trivial center. -/
def coreStarA7Equiv {G : Type*} [Group G] {K R : Subgroup G}
    (hRK : R ≤ normalizer K) (hb : FullSieve.StarKernelBound K R)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    (K ⧸ pCore 2 K) ≃* starImage K R K := by
  apply MulEquiv.ofBijective (coreToStar hRK)
  refine ⟨(MonoidHom.ker_eq_bot_iff _).mp ?_, coreToStar_surjective hRK⟩
  apply bot_unique
  intro x hx
  have hz := FullSieve.coreToStar_ker_le_center_of_bound hRK hb hx
  have hez : e x ∈ center (alternatingGroup (Fin 7)) :=
    (centerCongr e ⟨x, hz⟩).property
  rw [alternatingGroup.center_eq_bot (by simp)] at hez
  exact e.map_eq_one_iff.mp (mem_bot.mp hez)

/-- On representatives the isomorphism is the original star projection. -/
@[simp] theorem coreStarA7Equiv_mk {G : Type*} [Group G] {K R : Subgroup G}
    (hRK : R ≤ normalizer K) (hb : FullSieve.StarKernelBound K R)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) (k : K) :
    coreStarA7Equiv hRK hb e (QuotientGroup.mk' (pCore 2 K) k) =
      toStarImage K R k := rfl

/-- Every full C.2.7 alternative compatible with the actual A7 core marking
has a block module of order at most 64. Ordinary and exceptional A7 modules
both survive this bound. The non-block rows are ruled out through the
literal core-to-star isomorphism, rather than a change of quotient convention. -/
theorem module_card_le_of_c27_a7 {G : Type*} [Group G] [Finite G]
    {κ : GroupClass} {H K R MH : Subgroup G}
    (c27 : Conclusion κ H K R MH) (hRK : R ≤ normalizer K)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    Nat.card (BlockModule K) ≤ 2 ^ 6 := by
  have hc : Nat.card (K ⧸ pCore 2 K) = 2520 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hs : Nat.card (starImage K R K) = 2520 :=
    (Nat.card_congr (coreStarA7Equiv hRK c27.kernel.upper e).toEquiv).symm.trans hc
  cases c27.alternatives with
  | chi _ _ cases =>
    cases cases with
    | binary n hm _ _ => exact binary_module_card_le hc hm
    | five hm _ _ _ => exact alternating_module_card_le (by decide) (by decide) hm
    | sevenDihedral hm _ _ => exact alternating_module_card_le (by decide) (by decide) hm
    | sevenElementary hm _ _ => exact alternating_module_card_le (by decide) (by decide) hm
  | alternating n hl hu _ hm _ _ => exact alternating_module_card_le hl hu hm
  | ahatSix _ hm _ _ =>
    exact (Nat.card_le_card_of_surjective (QuotientGroup.mk' (blockFixed K))
      (QuotientGroup.mk'_surjective _)).trans_eq hm.2.2.2.2.1
  | exceptionalSeven _ hm _ =>
    rw [hm.module_card]
    norm_num
  | rankTwo _ cases =>
    rcases cases with ⟨hm, _⟩ | ⟨hm, _⟩
    · exact alternating_module_card_le (by decide) (by decide) hm
    · obtain ⟨_, F, _, _, hF, _, ⟨model⟩, _⟩ := hm
      have hsp := (Nat.card_congr model.quotientIso.toEquiv).symm.trans hc
      rw [Theory.SpecificGroups.SymplecticFour.card_sp, hF] at hsp
      norm_num at hsp
  | binaryG2 _ hm _ =>
    obtain ⟨_, _, ⟨model⟩, _⟩ := hm
    have he := Nat.card_congr model.moduleIso.toEquiv
    change Nat.card (BlockModule K) = Nat.card (Fin 6 → ZMod 2) at he
    rw [he, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  | linearThree n F hn hF hp _ =>
    obtain ⟨es, _⟩ := hp
    exact (not_sl_three_card F hn hF ((Nat.card_congr es.toEquiv).symm.trans hs)).elim
  | binaryLinear n hn hp =>
    obtain ⟨es, _⟩ := hp
    have he := (Nat.card_congr es.toEquiv).symm.trans hs
    rcases hn with rfl | rfl
    · have hd := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 4
      rw [he] at hd
      norm_num [Fin.prod_univ_succ] at hd
    · have hd := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
      rw [he] at hd
      norm_num [Fin.prod_univ_succ] at hd

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.AlternatingBound
