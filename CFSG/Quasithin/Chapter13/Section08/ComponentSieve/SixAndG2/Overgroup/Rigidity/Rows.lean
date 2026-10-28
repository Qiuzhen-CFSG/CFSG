module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup.Reduction
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection.LiftingOrders
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.JankoFour
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.SU3.PrimeOrderDivisibility
public import Theory.Mathieu.M11.Properties.Order
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# The constrained A.3.12 calculation for the three surviving components

The quotient of the smaller subgroup by its two-core and the larger subgroup
are among A₆, L₄(2), and G₂(2)′. Divisibility leaves only the possible A₆
section inside L₄(2). We inspect every actual A.3.12 embedding row to exclude
that proper inclusion, retaining the two-core in the smaller quotient.
In particular this does not assert that A₆ fails to embed abstractly in A₈.

The J₄ row uses its checked subgroup of order 2048, avoiding a full order
calculation. All other exclusions use the source row's actual model, normal
two-subgroup, or odd-core condition.

Source: Aschbacher–Smith, A.3.12 and 13.8.27(2), printed p.963.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup
open Chapter1.Section02 Chapter1.Section02.LocalModels
open Section06.TerminalContradiction.Components.CandidateSelection.LiftingOrders
variable {G : Type*} [Group G]

private theorem card_binary_four (h : ClassicalGroup.IsPSL G 4 2) : Nat.card G = 20160 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
  rw [hF] at hc
  norm_num [Fin.prod_univ_succ] at hc
  exact hc

private theorem survivor_card (h : Survivor G) :
    Nat.card G = 360 ∨ Nat.card G = 20160 ∨ Nat.card G = 6048 := by
  rcases h with h | h | h
  · obtain ⟨e⟩ := h
    left
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  · exact .inr (.inl (card_binary_four h))
  · obtain ⟨e⟩ := h
    right; right
    rw [Nat.card_congr e.toEquiv]
    exact Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)

private theorem remaining_survivor_case {X : Type*} [Group X] [Finite X]
    {B C : Subgroup X} (hle : B ≤ C) (hB : Survivor (B ⧸ pCore 2 B)) (hC : Survivor C) :
    B = C ∨ Nat.card (B ⧸ pCore 2 B) = 360 ∧ ClassicalGroup.IsPSL C 4 2 := by
  have hd := (card_quotient_dvd_card (pCore 2 B)).trans (card_dvd_of_le hle)
  have hqle : Nat.card (B ⧸ pCore 2 B) ≤ Nat.card B :=
    Nat.le_of_dvd Nat.card_pos (card_quotient_dvd_card (pCore 2 B))
  have hs := survivor_card hB
  rcases hC with hC | hC | hC
  · have he : Nat.card C = 360 := by
      obtain ⟨e⟩ := hC
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]; norm_num
    rcases hs with hs | hs | hs
    · left; exact eq_of_le_of_card_ge hle (by omega)
    · rw [hs,he] at hd; norm_num at hd
    · rw [hs,he] at hd; norm_num at hd
  · have he := card_binary_four hC
    rcases hs with hs | hs | hs
    · exact .inr ⟨hs,hC⟩
    · left; exact eq_of_le_of_card_ge hle (by omega)
    · rw [hs,he] at hd; norm_num at hd
  · have he : Nat.card C = 6048 := by
      obtain ⟨e⟩ := hC
      rw [Nat.card_congr e.toEquiv]
      exact Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)
    rcases hs with hs | hs | hs
    · rw [hs,he] at hd; norm_num at hd
    · rw [hs,he] at hd; norm_num at hd
    · left; exact eq_of_le_of_card_ge hle (by omega)

private theorem prime_dvd_binary_four {p : ℕ} (hp : p.Prime) (hd : p ∣ 20160) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  have he : 20160 = 2^6 * 3^2 * 5 * 7 := by norm_num
  rw [he] at hd
  rcases hp.dvd_mul.mp hd with hd | hd
  · rcases hp.dvd_mul.mp hd with hd | hd
    · rcases hp.dvd_mul.mp hd with hd | hd
      · exact .inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
      · exact .inr (.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hd)))
    · exact .inr (.inr (.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hd)))
  · exact .inr (.inr (.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hd)))

private theorem small_card (hd : 360 ∣ Nat.card G)
    (h : IsAlternating G 5 ∨ ClassicalGroup.IsPSL G 3 2) : False := by
  rcases h with h | h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at hd
    norm_num at hd
  · rw [card_linear_three h] at hd
    norm_num at hd

private theorem binary_four_oddCore [Finite G] (h : ClassicalGroup.IsPSL G 4 2) :
    pPrimeCore 2 G = ⊥ := by
  have hc := card_binary_four h
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 4) F) :=
    Atlas.psl_simple_high_rank 4 (by decide)
  let : IsSimpleGroup G := e.isSimpleGroup
  rcases (inferInstance : (pPrimeCore 2 G).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · have hp := pPrimeCore_coprime_card (p := 2) (G := G)
    rw [ht, card_top, hc] at hp
    norm_num at hp

private theorem no_psl_prime_small [Finite G] (hc : Nat.card (G ⧸ pCore 2 G) = 360)
    (hdiv : Nat.card G ∣ 20160) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL G 2 p) : False := by
  have hb := card_psl_two hm
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at ho
  have hpg : ¬ p ∣ Nat.gcd 2 (p - 1) := by
    intro hh
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (dvd_trans hh (Nat.gcd_dvd_left _ _)))
  have hpB : p ∣ Nat.card G := (hp.dvd_mul.mp
    (hb.symm ▸ (dvd_mul_right p (p ^ 2 - 1)))).resolve_right hpg
  have hd := Nat.le_of_dvd (Nat.card_pos (α := G)) (section_dvd hc)
  rcases prime_dvd_binary_four hp (hpB.trans hdiv) with rfl | rfl | rfl | rfl <;>
    norm_num at hb hp2 <;> omega

private theorem no_sl_prime_small [Finite G] (hc : Nat.card (G ⧸ pCore 2 G) = 360)
    (hdiv : Nat.card G ∣ 20160) {p : ℕ} (hp : p.Prime)
    (hm : IsSL G 2 p) : False := by
  have hb := card_sl_two hm
  have hpB : p ∣ Nat.card G := by rw [hb]; exact dvd_mul_right _ _
  have hd := section_dvd hc
  rcases prime_dvd_binary_four hp (hpB.trans hdiv) with rfl | rfl | rfl | rfl <;>
    rw [hb] at hd <;> norm_num at hd

private theorem six_in_binary_four {X : Type*} [Group X] [Finite X]
    {B C : Subgroup X} (hle : B ≤ C) (h : A312Embedding B C)
    (hc : Nat.card (B ⧸ pCore 2 B) = 360) (hC : ClassicalGroup.IsPSL C 4 2) : B = C := by
  have hcC := card_binary_four hC
  have hd : Nat.card B ∣ 20160 := hcC ▸ card_dvd_of_le hle
  have hdB := section_dvd hc
  have smallQ (N : Subgroup B) [N.Normal] (hN : IsPGroup 2 N)
      (hQ : IsAlternating (B ⧸ N) 5 ∨ ClassicalGroup.IsPSL (B ⧸ N) 3 2) : False :=
    small_card (section_dvd_quotient hc N hN) hQ
  cases h with
  | one eq => exact eq
  | two n hn small large residual =>
      have he := ChapterC.Section05.NormalizerControl.EmbeddingSelection.binary_card small
      rw [hc] at he
      have hn3 : n ≤ 3 := by
        by_contra hn3
        have hq : 16 ≤ 2^n := (show 16 = 2^4 by decide).le.trans
          (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 4 ≤ n))
        have hs : 255 ≤ (2^n)^2 - 1 :=
          Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
        nlinarith
      interval_cases n <;> norm_num at he
  | three m hm small large residual =>
      obtain ⟨e⟩ := small
      have hh : 3 ∣ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
        rw [← Nat.card_congr e.toEquiv, hc]; norm_num
      exact (BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m hm hh).elim
  | four small large residual => have hh := card_linear_three small; omega
  | five small large residual => have hh := card_binary_four small; omega
  | six small large => exact (small_card hdB small).elim
  | seven models =>
      rcases models with ⟨_, large⟩ | ⟨_, large⟩
      · obtain ⟨e⟩ := large
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at hcC
        norm_num at hcC
      · rw [card_cover large] at hcC; norm_num at hcC
  | eight models =>
      rcases models with ⟨p, hp, ho, _, small, _⟩ | ⟨p, hp, small, _⟩
      · exact (no_psl_prime_small hc hd hp ho small).elim
      · exact (small_card hdB (.inl small)).elim
  | nine models =>
      rcases models with ⟨p, _, hp, _, _, small, _⟩ | ⟨small, large⟩ | ⟨small, large⟩
      · exact (no_sl_prime_small hc hd hp small).elim
      · obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := large
        have hh : 5^3 ∣ Nat.card C := by
          rw [Nat.card_congr e.toEquiv]
          exact J.prime_cube_dvd_card_projective (by decide) hF hconj
        rw [hcC] at hh; norm_num at hh
      · rw [card_cover small] at hd; norm_num at hd
  | ten p hp ho hlarge small large =>
      obtain ⟨N, _, hN, hQ⟩ := small
      let : NeZero p := ⟨hp.ne_zero⟩
      have hb : Nat.card B = (p * (p^2 - 1)) * p^2 := by
        rw [card_eq_card_quotient_mul_card_subgroup N, card_sl_two hQ, card_elementary hN]
      have hpB : p ∣ Nat.card B := by rw [hb]; exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
      rcases prime_dvd_binary_four hp (hpB.trans hd) with rfl | rfl | rfl | rfl <;>
        rw [hb] at hdB <;> norm_num at hdB
  | eleven small large =>
      obtain ⟨e⟩ := large
      rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m11_order] at hcC
      norm_num at hcC
  | twelve models =>
      rcases models with ⟨_, ⟨e⟩⟩ | ⟨_, _, ⟨ez⟩, ⟨eq⟩⟩
      · rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m22_order] at hcC
        norm_num at hcC
      · rw [card_eq_card_quotient_mul_card_subgroup (center C),
          Nat.card_congr eq.toEquiv, Nat.card_congr ez.toEquiv, Sporadic.Mathieu.m22_order] at hcC
        norm_num at hcC
  | thirteen large small =>
      obtain ⟨e⟩ := large
      rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m23_order] at hcC
      norm_num at hcC
  | fourteen large small =>
      obtain ⟨e⟩ := large
      rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m24_order] at hcC
      norm_num at hcC
  | fifteen small large => exact (small_card hdB (.inl small)).elim
  | sixteen small large =>
      obtain ⟨N, _, hN, hQ⟩ := small
      exact (smallQ N (extraspecial_two hN) (.inl hQ)).elim
  | seventeen large small =>
      obtain ⟨e⟩ := large
      let K := Janko4.Cardinality.localKernel Janko4.matrixA_mul_self Janko4.matrixB_pow_four
      have hk : Nat.card K = 2048 := Janko4.Cardinality.localKernel_card _ _
      have hdiv : Nat.card K ∣ Nat.card Janko4.Model :=
        K.card_subgroup_dvd_card.trans (Janko4.Cardinality.max1Subgroup _ _).card_subgroup_dvd_card
      rw [hk, ← Nat.card_congr e.toEquiv, hcC] at hdiv
      norm_num at hdiv
  | eighteen large small =>
      rcases small with ⟨N, _, hN, hQ⟩ | ⟨N, _, ⟨e⟩, hQ⟩
      · exact (smallQ N (cyclicCentral_two hN) (.inl hQ)).elim
      · have hN : IsPGroup 2 N := IsPGroup.of_card (n := 6) (by
          rw [Nat.card_congr e.toEquiv]; norm_num)
        exact (smallQ N hN (.inr hQ)).elim
  | nineteen large small =>
      rcases small with ⟨N, _, hN, hQ⟩ | ⟨N, _, hN, hQ⟩
      · exact (smallQ N (extraspecial_two hN) (.inr hQ)).elim
      · rw [card_eq_card_quotient_mul_card_subgroup N, card_cover hQ, card_elementary hN] at hd
        norm_num at hd
  | twenty large small kernel =>
      exact (small_card (by rw [hc]) small).elim
  | twenty_one p hp ho noncentral generation quotient =>
      rw [binary_four_oddCore hC, commutator_bot_left] at noncentral
      exact (noncentral rfl).elim
  | twenty_two p hp noncentral large image =>
      rw [binary_four_oddCore hC, commutator_bot_left] at noncentral
      exact (noncentral rfl).elim

/-- Rigidity of the actual A.3.12 pair for the surviving quotient list. -/
theorem survivor_rigidity : SurvivorRigidity := by
  intro X _ _ B C hle he hB hC
  rcases remaining_survivor_case hle hB hC with hh | ⟨hc, hl⟩
  · exact hh
  · exact six_in_binary_four hle he hc hl

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Overgroup
