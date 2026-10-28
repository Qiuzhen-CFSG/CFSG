module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddRanks
public import CFSG.Quasithin.ChapterA.Section02.FiniteModelRankExclusions
public import Theory.SpecificGroups.SymplecticSix.OrderRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.Held.SylowOrderBound
public import Theory.Mathieu.M24.Properties.Order

/-!
# The original unitary residual in the full Theorem-B list

A component containing the whole six-space and its U₃(3) residual has
central quotient order divisible by 64 · 6048. The certified orders and
Sylow bounds exclude every finite exceptional model except J₄ and Ru.
The rank-six bound excludes every odd-characteristic family. All Bender
and rank-two characteristic-two models remain, with their literal markings.

Source: Aschbacher--Smith 4.4.11--12 and the final inspection on p.622.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory ChapterA.Section02 ClassificationModels

private theorem held_not_large_residual : ¬ 387072 ∣ Nat.card Held.He := by
  intro hd
  let P : Sylow 2 Held.He := Classical.choice inferInstance
  have hP := P.pow_dvd_card_of_pow_dvd_card (n := 11)
    ((by decide : 2^11 ∣ 387072).trans hd)
  have hl := Nat.le_of_dvd Nat.card_pos hP
  have hu := Held.sylow_card_le_1024 P
  norm_num at hl
  omega

private theorem sporadic_not_large_residual (n : SporadicName)
    (hJ : n ≠ .j4) (hR : n ≠ .ru) : ¬ 387072 ∣ Nat.card n.Carrier := by
  cases n with
  | m11 => change ¬387072 ∣ Nat.card Sporadic.Mathieu.M11; rw [Sporadic.Mathieu.m11_order]; norm_num
  | m12 => change ¬387072 ∣ Nat.card Sporadic.Mathieu.M12; rw [Sporadic.Mathieu.m12_order]; norm_num
  | m22 => change ¬387072 ∣ Nat.card Sporadic.Mathieu.M22; rw [Sporadic.Mathieu.m22_order]; norm_num
  | m23 => change ¬387072 ∣ Nat.card Sporadic.Mathieu.M23; rw [Sporadic.Mathieu.m23_order]; norm_num
  | m24 => change ¬387072 ∣ Nat.card Sporadic.Mathieu.M24; rw [Sporadic.Mathieu.m24_order]; norm_num
  | j2 => change ¬387072 ∣ Nat.card Sporadic.LeechRelated.J2.Carrier; rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]; norm_num
  | j3 => change ¬387072 ∣ Nat.card Sporadic.Janko3.Model; rw [Sporadic.Janko3.model_card]; norm_num
  | j4 => exact (hJ rfl).elim
  | hs =>
      exact fun hd => (by decide : ¬387072 ∣ 2^9*3^2*5^3*7*11)
        (hd.trans Sporadic.LeechRelated.HS.card_carrier_dvd)
  | he => exact held_not_large_residual
  | ru => exact (hR rfl).elim

/-- The complete B catalogue after the rank and residual-order exclusions.
No isomorphism is inferred from an order; all surviving markings are retained. -/
theorem unitary_residual_theoremB_models
    {Q : Type*} [Group Q] [Finite Q]
    (hm : IsTheoremBModel Q) (hr : 6 ≤ primeRank 2 Q)
    (hd : 387072 ∣ Nat.card Q) :
    IsBenderModel Q ∨ (∃ f, IsRankTwoModel Q f) ∨
      Nonempty (Q ≃* Janko4.Model) ∨ Nonempty (Q ≃* Rudvalis.Model) := by
  cases hm with
  | alternating n hn e =>
      obtain ⟨e⟩ := e
      rw [Nat.card_congr e.toEquiv] at hd
      have hf := hd.trans (alternatingGroup (Fin n)).card_subgroup_dvd_card
      rw [Nat.card_perm,Nat.card_fin] at hf
      exact False.elim ((by decide : ¬387072 ∣ Nat.factorial 9)
        (hf.trans (Nat.factorial_dvd_factorial hn)))
  | odd hm => exact (Chapter7.NormalizedSource.DoubledBinaryOddRanks.no_odd_model_of_rank_six hr hm).elim
  | bender hm => exact Or.inl hm
  | rank_two f hm => exact Or.inr (Or.inl ⟨f,hm⟩)
  | linear_binary n hn hm =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      rw [Nat.card_congr e.toEquiv] at hd
      rcases hn with rfl | rfl
      · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
        norm_num [hF,Fin.prod_univ_succ] at hc
        rw [hc] at hd
        norm_num at hd
      · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
        norm_num [hF,Fin.prod_univ_succ] at hc
        rw [hc] at hd
        norm_num at hd
  | symplectic_binary hm =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      rw [Nat.card_congr e.toEquiv] at hd
      have hh := hd.trans (center (Theory.SpecificGroups.SymplecticSix.Sp F)).card_quotient_dvd_card
      rw [Theory.SpecificGroups.SymplecticSix.card_sp_of_card_two hF] at hh
      norm_num at hh
  | sporadic hm =>
      rcases hm with ⟨n,⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
      · by_cases hj : n = .j4
        · subst n
          exact Or.inr (Or.inr (Or.inl ⟨e⟩))
        by_cases hu : n = .ru
        · subst n
          exact Or.inr (Or.inr (Or.inr ⟨e⟩))
        exact False.elim (sporadic_not_large_residual n hj hu ((Nat.card_congr e.toEquiv) ▸ hd))
      · rw [Nat.card_congr e.toEquiv,Janko1.card_model] at hd
        norm_num at hd
      · rw [Nat.card_congr e.toEquiv,
          Nat.card_congr Theory.SpecificGroups.McLaughlin.Multiplier.permutationModelEquiv.toEquiv,
          Atlas.Sporadic.McLaughlin.card] at hd
        norm_num [Atlas.Sporadic.McLaughlin.order] at hd

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
