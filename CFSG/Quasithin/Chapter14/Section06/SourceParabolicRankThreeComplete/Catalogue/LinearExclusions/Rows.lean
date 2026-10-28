module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.LinearExclusions.ModelOrders
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SourceAlternatives

/-!
# Excluding quotient order 20,160 from the full F.6.18 catalogue

A quotient of F* of order 20,160 forces the ambient Sylow two-subgroup to
have order divisible by 64. This excludes the small Sylow rows, including
both corrected rank-one alternatives and the unextended degree-three row.
The graph-extension row has an odd-prime cube in the central quotient.
In the Mathieu rows, quotient divisibility would force 20,160 to divide
95,040. These arguments retain both local labels and the actual common Sylow.

Source: Aschbacher--Smith original 14.6.10(5), p.1029, and F.6.18,
pp.309--310, including the corrected alternatives in FSource.SourceAlternative.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.LinearExclusions
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open FSource

/-- No full source row has central quotient of F* of order 20,160. -/
theorem source_not_central_card_20160 {D : Type*} [Group D] [Finite D]
    {A B : Subgroup D} {S : Sylow 2 D} (h : SourceAlternative A B S)
    (hc : Nat.card (generalizedFitting D ⧸ center (generalizedFitting D)) = 20160) :
    False := by
  have hdF : 20160 ∣ Nat.card (generalizedFitting D) := by
    rw [← hc]
    exact Subgroup.card_dvd_of_surjective (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _)
  have hd : 20160 ∣ Nat.card D := hdF.trans (card_subgroup_dvd_card _)
  have hS : 64 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card
    ((by norm_num : 2 ^ 6 ∣ 20160).trans hd)
  rcases h with (h | hr) | hr
  · cases h with
    | one hs _ _ _ =>
      obtain ⟨a⟩ := hs
      rw [Nat.card_congr a.toEquiv] at hS
      norm_num [C] at hS
    | two hm =>
      rcases hm with ha | ⟨N, hN, _, hNcard, _, ⟨a⟩⟩
      · obtain ⟨a⟩ := ha
        rw [Nat.card_congr a.toEquiv] at hd
        norm_num [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_perm] at hd
      · let : N.Normal := hN
        have horder := Subgroup.card_eq_card_quotient_mul_card_subgroup N
        rw [Nat.card_congr a.toEquiv, hNcard] at horder
        norm_num [E4, C, Nat.card_prod] at horder
        rw [horder] at hd
        norm_num at hd
    | three _ hs _ _ =>
      obtain ⟨a⟩ := hs
      rw [Nat.card_congr a.toEquiv, DihedralGroup.nat_card] at hS
      norm_num at hS
    | four _ _ _ _ _ _ hs _ _ =>
      obtain ⟨a⟩ := hs
      rw [Nat.card_congr a.toEquiv] at hS
      norm_num [E4, C, Nat.card_prod] at hS
    | five _ _ _ _ _ _ hs _ _ =>
      obtain ⟨a⟩ := hs
      rw [Nat.card_congr a.toEquiv, DihedralGroup.nat_card] at hS
      norm_num at hS
    | six _ _ _ hs _ _ =>
      obtain ⟨a⟩ := hs
      rw [Nat.card_congr a.toEquiv, DihedralGroup.nat_card] at hS
      norm_num at hS
    | seven _ _ hs _ _ =>
      obtain ⟨a⟩ := hs
      rw [Nat.card_congr a.toEquiv, DihedralGroup.nat_card] at hS
      norm_num at hS
    | eight _ _ hs _ _ =>
      obtain ⟨a⟩ := hs
      rw [Nat.card_congr a.toEquiv, Nat.card_prod, DihedralGroup.nat_card] at hS
      norm_num [C] at hS
    | nine _ _ hs _ _ =>
      obtain ⟨a⟩ := hs
      rw [Nat.card_congr a.toEquiv, Nat.card_prod, DihedralGroup.nat_card] at hS
      norm_num [C] at hS
    | ten _ _ _ _ _ _ hs _ _ =>
      obtain ⟨a⟩ := hs
      rw [Nat.card_congr a.toEquiv, RegularWreathProduct.card] at hS
      norm_num [C] at hS
    | eleven r _ _ _ _ =>
      have hcub := degreeThree_central_prime_cube r.prime_isPrime
        (show r.prime ≠ 2 by have hm := r.congruence; omega) r.model.model
      rw [hc] at hcub
      exact no_odd_prime_cube_20160 r.prime_isPrime (by have hm := r.congruence; omega) hcub
    | twelve a _ _ _ _ =>
      rw [Nat.card_congr a.toEquiv, Sporadic.Mathieu.m12_order] at hd
      norm_num at hd
    | thirteen _ a _ _ _ _ =>
      rw [Nat.card_congr a.toEquiv, Sporadic.Mathieu.m12_order] at hdF
      norm_num at hdF
  · obtain ⟨r⟩ := hr
    obtain ⟨a⟩ := r.sylow
    rw [Nat.card_congr a.toEquiv, DihedralGroup.nat_card] at hS
    norm_num at hS
  · obtain ⟨r⟩ := hr
    obtain ⟨a⟩ := r.sylow
    rw [Nat.card_congr a.toEquiv, Nat.card_prod, DihedralGroup.nat_card] at hS
    norm_num [C] at hS

end CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.LinearExclusions
