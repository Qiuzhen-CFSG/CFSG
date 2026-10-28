module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection.LiftingOrders
/-!
# The exceptional two-core section sieve in A.3.12

The three exceptional section orders exclude all proper embedding rows except
M₂₃. The equal-order PSL₄(2) case retains its separate model distinction.
This is the exact sieve used by the component lifting in 13.6.27, p.934.
-/
@[expose] public section
noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection
open Chapter1.Section02 Chapter1.Section02.LocalModels LiftingOrders
variable {G : Type*} [Group G]

private theorem card_binary_four (h : ClassicalGroup.IsPSL G 4 2) : Nat.card G = 20160 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
  rw [hF] at hc
  norm_num [Fin.prod_univ_succ] at hc
  exact hc

variable [Finite G]
private theorem no_binary_quotient {m : ℕ} (hm : ExceptionalOrder m)
    (hc : Nat.card (G ⧸ pCore 2 G) = m)
    (hb : ¬ ClassicalGroup.IsPSL (G ⧸ pCore 2 G) 4 2)
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hQ : ClassicalGroup.IsPSL (G ⧸ N) 4 2) : False := by
  have hd := section_dvd_quotient hc N hN
  rw [card_binary_four hQ] at hd
  have hm : m = 20160 := by rcases hm with h | rfl | rfl; exact h; all_goals norm_num at hd
  have he := eq_twoCore_of_quotient_card N hN ((card_binary_four hQ).trans (hc.trans hm).symm)
  subst N
  exact hb hQ

private theorem no_binary_model {m : ℕ} (hm : ExceptionalOrder m)
    (hc : Nat.card (G ⧸ pCore 2 G) = m)
    (hb : ¬ ClassicalGroup.IsPSL (G ⧸ pCore 2 G) 4 2)
    (h : ClassicalGroup.IsPSL G 4 2) : False := by
  apply no_binary_quotient hm hc hb (⊥ : Subgroup G) (IsPGroup.of_card (n := 0) (by simp))
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  exact ⟨F, inferInstance, inferInstance, hF, ⟨QuotientGroup.quotientBot.trans e⟩⟩

/-- Every listed exceptional two-core section is unchanged, or lies in the
actual M₂₃ model. This conclusion deliberately retains the useful M₂₃ branch. -/
theorem lifting_alternatives_of_section_order {X : Type*} [Group X] [Finite X]
    {B K : Subgroup X} (hBK : B ≤ K) {m : ℕ} (hm : ExceptionalOrder m)
    (hc : Nat.card (B ⧸ pCore 2 B) = m)
    (hb : ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (h : A312Embedding B K) : B = K ∨ Nonempty (K ≃* Sporadic.Mathieu.M23) := by
  have hd := (common_divisor hm).trans (section_dvd hc)
  have hq : 20160 ∣ Nat.card (B ⧸ pCore 2 B) := by rw [hc]; exact common_divisor hm
  have smallQ (N : Subgroup B) [N.Normal] (hN : IsPGroup 2 N)
      (hQ : IsAlternating (B ⧸ N) 5 ∨ IsAlternating (B ⧸ N) 6 ∨
        IsAlternating (B ⧸ N) 7 ∨ IsAlternatingCover (B ⧸ N) 6 ∨
        ClassicalGroup.IsPSL (B ⧸ N) 3 2) : False :=
    no_small_model ((common_divisor hm).trans (section_dvd_quotient hc N hN)) hQ
  cases h with
  | one eq => exact Or.inl eq
  | two n hn small large residual => exact (no_binary_rank_one hm hc small).elim
  | three m hm' small large residual =>
      obtain ⟨f⟩ := small
      have h3 : 3 ∣ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
        rw [← Nat.card_congr f.toEquiv]
        exact dvd_trans (by norm_num : 3 ∣ 20160) hq
      exact (BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m hm' h3).elim
  | four small large residual => exact (no_small_model hq (by tauto)).elim
  | five small large residual => exact (hb small).elim
  | six small large => exact (no_small_model hd (by tauto)).elim
  | seven models =>
      rcases models with ⟨small, _⟩ | ⟨small, _⟩ <;> exact (no_small_model hd (by tauto)).elim
  | eight models =>
      rcases models with ⟨p, hp, ho, _, small, _⟩ | ⟨p, hp, small, _⟩
      · exact (no_psl_prime hm hc hp ho small).elim
      · exact (no_small_model hd (by tauto)).elim
  | nine models =>
      rcases models with ⟨p, _, hp, _, _, small, _⟩ | ⟨small, _⟩ | ⟨small, _⟩
      · exact (no_sl_prime hm hc hp small).elim
      · exact (no_small_model hd (by tauto)).elim
      · exact (no_small_model hd (by tauto)).elim
  | ten p hp ho hlarge small large => exact (no_odd_extension hm hc hp small).elim
  | eleven small large => exact (no_small_model hd (by tauto)).elim
  | twelve models =>
      rcases models with ⟨⟨N, _, hN, hQ⟩, _⟩ | ⟨⟨N, _, hN, hQ⟩, _⟩ <;>
        exact (smallQ N (elementary_two hN) (by tauto)).elim
  | thirteen large small => exact Or.inr large
  | fourteen large small =>
      rcases small with ⟨N, _, hN, hQ⟩ | ⟨N, _, hN, hQ⟩ | ⟨N, _, hN, hQ⟩
      · exact (no_binary_quotient hm hc hb N (elementary_two hN) hQ).elim
      · exact (smallQ N (elementary_two hN) (by tauto)).elim
      · exact (smallQ N (extraspecial_two hN) (by tauto)).elim
  | fifteen small large => exact (no_small_model hd (by tauto)).elim
  | sixteen small large =>
      obtain ⟨N, _, hN, hQ⟩ := small
      exact (smallQ N (extraspecial_two hN) (by tauto)).elim
  | seventeen large small =>
      rcases small with ⟨N, _, hN, hQ⟩ | ⟨N, _, hN, ⟨f⟩⟩ | hQ | hQ | hQ | hQ
      · obtain ⟨_, ⟨ez⟩, ⟨eq⟩⟩ := hQ
        have hQc : Nat.card (B ⧸ N) = 443520 * 3 := by
          rw [card_eq_card_quotient_mul_card_subgroup (center (B ⧸ N)),
            Nat.card_congr eq.toEquiv, Nat.card_congr ez.toEquiv, Sporadic.Mathieu.m22_order]
          simp
        have hdiv := (common_divisor hm).trans (section_dvd_quotient hc N (extraspecial_two hN))
        rw [hQc] at hdiv
        have hcQ := section_card_quotient hc N (extraspecial_two hN)
        obtain ⟨n, hn⟩ := card_shape hcQ
        have hn7 : n ≤ 7 := by
          by_contra hh
          have hp : 256 ≤ 2^n := (show 256 = 2^8 by norm_num).le.trans
            (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega : 8 ≤ n))
          rcases hm with rfl | rfl | rfl <;> nlinarith
        interval_cases n <;> rcases hm with rfl | rfl | rfl <;> norm_num at hn <;> omega
      · exact (no_mathieu_small hm (section_card_quotient hc N (elementary_two hN))
          (Or.inr ((Nat.card_congr f.toEquiv).trans Sporadic.Mathieu.m24_order))).elim
      · exact (no_small_model hq (by tauto)).elim
      · exact (no_small_model hq (by tauto)).elim
      · exact (hb hQ).elim
      · exact (no_small_model hq (by tauto)).elim
  | eighteen large small =>
      rcases small with ⟨N, _, hN, hQ⟩ | ⟨N, _, ⟨f⟩, hQ⟩
      · exact (smallQ N (cyclicCentral_two hN) (by tauto)).elim
      · have hN : IsPGroup 2 N := IsPGroup.of_card (n := 6) (by
          rw [Nat.card_congr f.toEquiv]; norm_num)
        exact (smallQ N hN (by tauto)).elim
  | nineteen large small =>
      rcases small with ⟨N, _, hN, hQ⟩ | ⟨N, _, hN, hQ⟩
      · exact (smallQ N (extraspecial_two hN) (by tauto)).elim
      · exact (smallQ N (elementary_two hN) (by tauto)).elim
  | twenty large small kernel => exact (no_small_model hq (by tauto)).elim
  | twenty_one p hp ho noncentral generation quotient =>
      exact (not_oddCore_supplement hBK hm hc hp generation quotient).elim
  | twenty_two p hp noncentral large image =>
      exact (not_oddCore_image_five hBK hm hc image).elim

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection
