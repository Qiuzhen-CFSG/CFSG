module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.ActorPruning.SmallRows
public import GorensteinWalter.PGL2Cardinality

/-!
# Rank-one offender actors and the early Goldschmidt rows

A binary SL₂ actor inside a group with Sylow two-subgroup of order at most
8 has field degree at most 3; a bound of 16 permits degree 4. Together with
S₅, their orders are therefore 60, 120, 504, and (under the second bound)
4080. The literal offender inclusion gives divisibility, while the two-group
quotient preserves all odd divisors.

These order restrictions exclude F.6.18(2)–(9) using the actual model maps.
The prime-field rows require a prime greater than 7. The remaining odd SL₂
parameters reduce to 7, 9, and 25, each excluded by its order or odd divisors.
Triple covers contribute a factor 27, and the degree-seven permutation rows
contribute 35. Every local clause in the surviving rows is retained, with
either orientation of the generating pair. No group is recognized by order.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, F.6.18(2–9),
pp.309–310, compared with B.5.1/B.5.6, pp.99–110, in 15.4.18, p.1163.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace QuasisimpleComparison.ActorPruning.RankOneRows
open FFAlternatives GoldschmidtAlternatives
variable {D : Type*} [Group D] [Finite D]
variable {A : Type*} [Group A]

private theorem linear_degree_bound (F : BinaryField) (i : SL(2,F.Carrier) →* D)
    (hi : Function.Injective i) (S : Sylow 2 D) {k : ℕ} (hs : Nat.card S ≤ 2 ^ k) :
    F.degree ≤ k := by
  have hd : 2 ^ F.degree ∣ Nat.card SL(2,F.Carrier) := by
    rw [GorensteinWalter.sl2_card_formula, F.card_eq]
    exact dvd_mul_right _ _
  have hb := S.pow_dvd_card_of_pow_dvd_card
    (hd.trans (card_dvd_of_injective i hi))
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    ((Nat.le_of_dvd (Nat.card_pos (α := S)) hb).trans hs)

private theorem card_cases_eight (ha : RankOneActorModel A)
    (i : A →* D) (hi : Function.Injective i) (S : Sylow 2 D) (hs : Nat.card S ≤ 8) :
    Nat.card A = 60 ∨ Nat.card A = 120 ∨ Nat.card A = 504 := by
  cases ha with
  | linearTwo F hlo _ e =>
    have hn := linear_degree_bound F (i.comp e.symm.toMonoidHom)
      (hi.comp e.symm.injective) S (k := 3) hs
    rw [Nat.card_congr e.toEquiv, GorensteinWalter.sl2_card_formula, F.card_eq]
    interval_cases hd : F.degree <;> norm_num
  | symmetricFive e =>
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

private theorem card_cases_sixteen (ha : RankOneActorModel A)
    (i : A →* D) (hi : Function.Injective i) (S : Sylow 2 D) (hs : Nat.card S ≤ 16) :
    Nat.card A = 60 ∨ Nat.card A = 120 ∨ Nat.card A = 504 ∨ Nat.card A = 4080 := by
  cases ha with
  | linearTwo F hlo _ e =>
    have hn := linear_degree_bound F (i.comp e.symm.toMonoidHom)
      (hi.comp e.symm.injective) S (k := 4) hs
    rw [Nat.card_congr e.toEquiv, GorensteinWalter.sl2_card_formula, F.card_eq]
    interval_cases hd : F.degree <;> norm_num
  | symmetricFive e =>
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

private theorem prime_support_eight {p n : ℕ} (hp : p.Prime) (ho : Odd p)
    (hc : n = 60 ∨ n = 120 ∨ n = 504) (hd : p ∣ n) : p = 3 ∨ p = 5 ∨ p = 7 := by
  have hd' : p ∣ 2 * 2 * 2 * 3 * 3 * 5 * 7 := hd.trans (by
    rcases hc with rfl | rfl | rfl <;> norm_num)
  have hne : p ≠ 2 := by intro h; subst p; norm_num at ho
  simpa only [hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp Nat.prime_two,
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    hne, false_or, or_assoc, or_self_left] using hd'

private theorem prime_support_sixteen {p n : ℕ} (hp : p.Prime) (ho : Odd p)
    (hc : n = 60 ∨ n = 120 ∨ n = 504 ∨ n = 4080) (hd : p ∣ n) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 17 := by
  have hd' : p ∣ 2 * 2 * 2 * 2 * 3 * 3 * 5 * 7 * 17 := hd.trans (by
    rcases hc with rfl | rfl | rfl | rfl <;> norm_num)
  have hne : p ≠ 2 := by intro h; subst p; norm_num at ho
  simpa only [hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp Nat.prime_two,
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 17),
    hne, false_or, or_assoc, or_self_left] using hd'

private theorem not_dvd_small_orders (ha : RankOneActorModel A) {m : ℕ}
    (hm : m = 36 ∨ m = 108 ∨ m = 168) : ¬ Nat.card A ∣ m := by
  cases ha with
  | linearTwo F hlo hhi e =>
    rw [Nat.card_congr e.toEquiv, GorensteinWalter.sl2_card_formula, F.card_eq]
    interval_cases hd : F.degree <;> rcases hm with rfl | rfl | rfl <;> norm_num
  | symmetricFive e =>
    rw [Nat.card_congr e.toEquiv]
    rcases hm with rfl | rfl | rfl <;>
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

private theorem psl_card_twice {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSL A 2 q) :
    Nat.card A * 2 = q * (q ^ 2 - 1) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  rw [Nat.card_congr e.toEquiv, ← hF]
  exact Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (hF ▸ ho)

private theorem psl_field_dvd {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSL A 2 q) :
    q ∣ Nat.card A := by
  apply (Nat.coprime_two_right.mpr ho).dvd_of_dvd_mul_right
  rw [psl_card_twice ho hm]
  exact dvd_mul_right _ _

private theorem triple_alternating_cube {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hc : TripleAlternating A n) : 27 ∣ Nat.card A := by
  obtain ⟨_, ⟨e⟩, ⟨q⟩⟩ := hc
  have hh : Nat.card A = Nat.card (center A) * Nat.card (A ⧸ center A) := by
    rw [← Subgroup.index_eq_card, Subgroup.card_mul_index]
  rw [hh, Nat.card_congr e.toEquiv, Nat.card_congr q.toEquiv]
  rcases hn with rfl | rfl <;> rw [nat_card_alternatingGroup] <;>
    norm_num [C, Nat.factorial]

private theorem triple_symmetric_cube {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hc : TripleSymmetric A n) : 27 ∣ Nat.card A := by
  obtain ⟨f, hf, ⟨e⟩, _⟩ := hc
  have hh := Extension.card (show Extension A (C 3) (Equiv.Perm (Fin n)) from ⟨f, hf, ⟨e⟩⟩)
  rw [hh]
  rcases hn with rfl | rfl <;>
    norm_num [C, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

end QuasisimpleComparison.ActorPruning.RankOneRows

universe u v
variable {D : Type u} [Group D] [Finite D]
    {K : GroupClass.{u}} {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D}
attribute [local instance] offenderSubgroup_normal
namespace QuasisimpleComparison.ActorPruning.RankOneRows
open GoldschmidtAlternatives

private theorem sylow_bound (ht : ChapterF.IsGoldschmidtTriple G₁ G₂) {m : ℕ}
    (hc : Nat.card (G₁ ⊓ G₂ : Subgroup D) ≤ m) : ∃ S : Sylow 2 D, Nat.card S ≤ m := by
  obtain ⟨S, hS⟩ := ht.intersection_sylow
  exact ⟨S, (Nat.card_congr (MulEquiv.subgroupCongr hS).toEquiv).symm.le.trans hc⟩

private theorem prime_eight (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (ha : RankOneActorModel (offenderSubgroup ρ)) (S : Sylow 2 D) (hs : Nat.card S ≤ 8)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ Nat.card D) :
    p = 3 ∨ p = 5 ∨ p = 7 :=
  prime_support_eight hp ho (card_cases_eight ha (offenderSubgroup ρ).subtype
    Subtype.val_injective S hs) ((h.odd_dvd_offender_card_iff ho).mpr hd)

private theorem prime_sixteen (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (ha : RankOneActorModel (offenderSubgroup ρ)) (S : Sylow 2 D) (hs : Nat.card S ≤ 16)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ Nat.card D) :
    p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 17 :=
  prime_support_sixteen hp ho (card_cases_sixteen ha (offenderSubgroup ρ).subtype
    Subtype.val_injective S hs) ((h.odd_dvd_offender_card_iff ho).mpr hd)

private theorem not_odd_product (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (ha : RankOneActorModel (offenderSubgroup ρ)) (S : Sylow 2 D) (hs : Nat.card S ≤ 16)
    {m : ℕ} (hm : m = 35 ∨ m = 45) : ¬ m ∣ Nat.card D := by
  intro hd
  have ho : Odd m := by rcases hm with rfl | rfl <;> decide
  have hn := (h.odd_dvd_offender_card_iff ho).mpr hd
  rcases card_cases_sixteen ha (offenderSubgroup ρ).subtype Subtype.val_injective S hs
    with hc | hc | hc | hc <;> rw [hc] at hn <;>
    rcases hm with rfl | rfl <;> norm_num at hn

omit [Finite D] in
private theorem not_case2 (ha : RankOneActorModel (offenderSubgroup ρ)) (hr : Case2 D) : False := by
  have hc : Nat.card D = 36 ∨ Nat.card D = 108 ∨ Nat.card D = 168 := by
    rcases hr with hr | hr
    · obtain ⟨e⟩ := hr
      left
      rw [Nat.card_congr e.toEquiv]
      norm_num [S3, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    · right; left
      rw [hr.card, HeisenbergPrime.card]
      norm_num [E4, C, Nat.card_prod]
  exact not_dvd_small_orders ha hc (offenderSubgroup ρ).card_subgroup_dvd_card

private theorem not_case3 (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (ha : RankOneActorModel (offenderSubgroup ρ))
    (ht : ChapterF.IsGoldschmidtTriple G₁ G₂) (hr : Case3 G₁ G₂) : False := by
  obtain ⟨p, A, B, hp, hm, hA, _, _, _, _, ⟨e⟩, _⟩ := hr
  obtain ⟨S, hs⟩ := sylow_bound ht (m := 8) (by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card])
  have ho : Odd p := Nat.odd_iff.mpr (by omega)
  have hd := (psl_field_dvd ho hA).trans A.card_subgroup_dvd_card
  have hh := prime_eight h ha S hs hp ho hd
  omega

private theorem not_case4 (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (ha : RankOneActorModel (offenderSubgroup ρ))
    (ht : ChapterF.IsGoldschmidtTriple G₁ G₂) (hr : Case4 G₁ G₂) : False := by
  obtain ⟨p, hp, hm, hA, ⟨e⟩, _⟩ := hr
  obtain ⟨S, hs⟩ := sylow_bound ht (m := 8) (by
    rw [Nat.card_congr e.toEquiv]; norm_num [E4, C, Nat.card_prod])
  have ho : Odd p := Nat.odd_iff.mpr (by omega)
  have hh := prime_eight h ha S hs hp ho (psl_field_dvd ho hA)
  omega

private theorem not_case5 (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (ha : RankOneActorModel (offenderSubgroup ρ))
    (ht : ChapterF.IsGoldschmidtTriple G₁ G₂) (hr : Case5 G₁ G₂) : False := by
  obtain ⟨p, hp, hm, ⟨F, _, _, hF, ⟨a⟩⟩, ⟨e⟩, _⟩ := hr
  obtain ⟨S, hs⟩ := sylow_bound ht (m := 8) (by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card])
  have hd : p ∣ Nat.card D := by
    rw [Nat.card_congr a.toEquiv, GorensteinWalter.pgl2_card_formula, hF]
    exact dvd_mul_right _ _
  have hh := prime_eight h ha S hs hp (Nat.odd_iff.mpr (by omega)) hd
  omega

private theorem not_case6 (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (ha : RankOneActorModel (offenderSubgroup ρ))
    (ht : ChapterF.IsGoldschmidtTriple G₁ G₂) (hr : Case6 G₁ G₂) : False := by
  obtain ⟨hr, ⟨e⟩, _⟩ := hr
  rcases hr with hc | ⟨p, n, hp, hn, hle, hm, hc⟩
  · exact h.rankOne_not_odd_prime_cube ha (by decide : Nat.Prime 3) (by decide)
      (triple_alternating_cube (Or.inl rfl) hc)
  obtain ⟨S, hs⟩ := sylow_bound ht (m := 8) (by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card])
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    interval_cases n <;> norm_num at hm
  have ho := hp.odd_of_ne_two hp2
  have hd : p ∣ Nat.card D := (dvd_pow_self p (by omega : n ≠ 0)).trans
    (psl_field_dvd ho.pow hc)
  have hh := prime_eight h ha S hs hp ho hd
  rcases hh with rfl | rfl | rfl <;> interval_cases n <;> norm_num at hm
  · have hh := psl_card_twice (by decide : Odd (3 ^ 2)) hc
    have hcard : Nat.card D = 360 := by norm_num at hh; omega
    exact not_odd_product h ha S (hs.trans (by decide)) (Or.inr rfl)
      (by rw [hcard]; decide)
  · have hh := psl_card_twice (by decide : Odd (5 ^ 2)) hc
    have hcard : Nat.card D = 7800 := by norm_num at hh; omega
    have hh := prime_eight h ha S hs (by decide : Nat.Prime 13)
      (by decide : Odd 13) (by rw [hcard]; decide)
    norm_num at hh
  · have hh := psl_card_twice (by decide : Odd (7 ^ 1)) hc
    have hcard : Nat.card D = 168 := by norm_num at hh; omega
    exact not_dvd_small_orders ha (Or.inr (Or.inr hcard))
      (offenderSubgroup ρ).card_subgroup_dvd_card

private theorem not_case7 (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (ha : RankOneActorModel (offenderSubgroup ρ))
    (ht : ChapterF.IsGoldschmidtTriple G₁ G₂) (hr : Case7 G₁ G₂) : False := by
  obtain ⟨hr, ⟨e⟩, _⟩ := hr
  rcases hr with hr | hc
  · obtain ⟨a⟩ := hr
    obtain ⟨S, hs⟩ := sylow_bound ht (m := 16) (by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]; decide)
    exact not_odd_product h ha S hs (Or.inl rfl) (by
      rw [Nat.card_congr a.toEquiv, nat_card_alternatingGroup]; norm_num [Nat.factorial])
  · exact h.rankOne_not_odd_prime_cube ha (by decide : Nat.Prime 3) (by decide)
      (triple_alternating_cube (Or.inr rfl) hc)

private theorem not_case8 (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (ha : RankOneActorModel (offenderSubgroup ρ))
    (ht : ChapterF.IsGoldschmidtTriple G₁ G₂) (hr : Case8 G₁ G₂) : False := by
  obtain ⟨hr, ⟨e⟩, _⟩ := hr
  rcases hr with hc | ⟨p, hp, hm, F, _, _, hF, σ, _, i, t, hi, hind, _⟩
  · exact h.rankOne_not_odd_prime_cube ha (by decide : Nat.Prime 3) (by decide)
      (triple_symmetric_cube (Or.inl rfl) hc)
  obtain ⟨S, hs⟩ := sylow_bound ht (m := 16) (by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, DihedralGroup.nat_card]; norm_num [C])
  have ho : Odd p := Nat.odd_iff.mpr (by omega)
  have hc : ClassicalGroup.IsPSL PSL(2,F) 2 (p ^ 2) := ⟨F, inferInstance, inferInstance,
    hF, ⟨MulEquiv.refl _⟩⟩
  have hd : p ∣ Nat.card D := (dvd_pow_self p (by decide : 2 ≠ 0)).trans
    ((psl_field_dvd ho.pow hc).trans (card_dvd_of_injective i hi))
  have hh := prime_sixteen h ha S hs hp ho hd
  have he : p = 3 := by omega
  subst p
  have hh := psl_card_twice (by decide : Odd (3 ^ 2)) hc
  have hc' : Nat.card PSL(2,F) = 360 := by norm_num at hh; omega
  exact not_odd_product h ha S hs (Or.inr rfl)
    ((show 45 ∣ Nat.card PSL(2,F) by rw [hc']; decide).trans
      (card_dvd_of_injective i hi))

private theorem not_case9 (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (ha : RankOneActorModel (offenderSubgroup ρ))
    (ht : ChapterF.IsGoldschmidtTriple G₁ G₂) (hr : Case9 G₁ G₂) : False := by
  obtain ⟨hr, ⟨e⟩, _⟩ := hr
  rcases hr with hr | hc
  · obtain ⟨a⟩ := hr
    obtain ⟨S, hs⟩ := sylow_bound ht (m := 16) (by
      rw [Nat.card_congr e.toEquiv, Nat.card_prod, DihedralGroup.nat_card]; norm_num [C])
    exact not_odd_product h ha S hs (Or.inl rfl) (by
      rw [Nat.card_congr a.toEquiv]
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial])
  · exact h.rankOne_not_odd_prime_cube ha (by decide : Nat.Prime 3) (by decide)
      (triple_symmetric_cube (Or.inr rfl) hc)

private theorem ordered_rows (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (ha : RankOneActorModel (offenderSubgroup ρ)) (hr : RemainingOrdered G₁ G₂) :
    LargeRowsOrdered G₁ G₂ := by
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr
  · exact (not_case2 ha hr).elim
  · exact (not_case3 h ha h.triple hr).elim
  · exact (not_case4 h ha h.triple hr).elim
  · exact (not_case5 h ha h.triple hr).elim
  · exact (not_case6 h ha h.triple hr).elim
  · exact (not_case7 h ha h.triple hr).elim
  · exact (not_case8 h ha h.triple hr).elim
  · exact (not_case9 h ha h.triple hr).elim
  · exact Or.inl hr
  · exact Or.inr (Or.inl hr)
  · exact Or.inr (Or.inr (Or.inl hr))
  · exact Or.inr (Or.inr (Or.inr hr))

end QuasisimpleComparison.ActorPruning.RankOneRows

/-- A bounded binary rank-one offender actor excludes F.6.18(2)–(9).
The comparison uses its actual normal inclusion and the two-group quotient,
retaining every source clause of rows (10)–(13) in either orientation. -/
theorem ProjectiveLine.ClassifiedAction.rankOneActor_rows
    (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (_b : QuasisimpleComparison.BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype))
    (ha : QuasisimpleComparison.ActorPruning.RankOneActorModel (offenderSubgroup ρ)) :
    QuasisimpleComparison.ActorPruning.LargeRows G₁ G₂ := by
  rcases h.goldschmidt with hr | hr
  · exact Or.inl (QuasisimpleComparison.ActorPruning.RankOneRows.ordered_rows h ha hr)
  · have hs : ProjectiveLine.ClassifiedAction K ρ G₂ G₁ :=
      { h with triple := h.triple.symm, goldschmidt := Or.inl hr }
    exact Or.inr (QuasisimpleComparison.ActorPruning.RankOneRows.ordered_rows hs ha hr)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
