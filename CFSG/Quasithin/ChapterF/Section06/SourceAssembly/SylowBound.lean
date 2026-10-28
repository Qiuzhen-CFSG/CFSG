module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SourceAlternatives

/-!
# The common Sylow bound in all corrected F.6.18 alternatives

Each original row gives the common Sylow group explicitly. The two extra
rank-one field alternatives give dihedral or dihedral-times-cyclic groups.
Consequently its order is at most 128. This extracts the row calculation
used in the Chapter 15 comparison without requiring that comparison's
additional module hypotheses.

The original Chapter 13 point-span application transports this bound through
the canonical common Sylow isomorphism between the action and O₃′ quotients.
Source: Aschbacher--Smith F.6.18, printed pp.309--310; adapted from
ClassificationComparison/FullSource/Basic.lean.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
universe u

private theorem extension_card {A B C : Type*} [Group A] [Group B] [Group C]
    (h : Extension A B C) : Nat.card A = Nat.card B * Nat.card C := by
  obtain ⟨N,_,⟨e⟩,⟨f⟩⟩ := h
  rw [card_eq_card_quotient_mul_card_subgroup N, Nat.card_congr e.toEquiv,
    Nat.card_congr f.toEquiv, Nat.mul_comm]

private theorem alternative_sylow_bound {D : Type u} [Group D] [Finite D]
    {G₁ G₂ : Subgroup D} {S : Sylow 2 D} (r : Alternative G₁ G₂ S) :
    Nat.card S ≤ 128 := by
  cases r with
  | one hs _ _ _ =>
    rw [Nat.card_congr hs.some.toEquiv]; norm_num [C]
  | two hm =>
    apply (Nat.card_le_card_of_injective (S : Subgroup D).subtype Subtype.val_injective).trans
    rcases hm with he | ⟨N,_,_,hc,_,⟨e⟩⟩
    · obtain ⟨e⟩ := he
      rw [Nat.card_congr e.toEquiv]
      norm_num [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    · rw [card_eq_card_quotient_mul_card_subgroup N, hc, Nat.card_congr e.toEquiv]
      norm_num [E4, C, Nat.card_prod]
  | three _ hs _ _ =>
    rw [Nat.card_congr hs.some.toEquiv, DihedralGroup.nat_card]; norm_num
  | five _ _ _ _ _ _ hs _ _ =>
    rw [Nat.card_congr hs.some.toEquiv, DihedralGroup.nat_card]; norm_num
  | six _ _ _ hs _ _ =>
    rw [Nat.card_congr hs.some.toEquiv, DihedralGroup.nat_card]; norm_num
  | seven _ _ hs _ _ =>
    rw [Nat.card_congr hs.some.toEquiv, DihedralGroup.nat_card]; norm_num
  | four _ _ _ _ _ _ hs _ _ =>
    rw [Nat.card_congr hs.some.toEquiv]; norm_num [E4, C, Nat.card_prod]
  | eight _ _ hs _ _ | nine _ _ hs _ _ =>
    rw [Nat.card_congr hs.some.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
    norm_num [C]
  | ten _ _ _ _ _ _ hs _ _ =>
    rw [Nat.card_congr hs.some.toEquiv]
    norm_num [W32, C, RegularWreathProduct.card]
  | eleven _ _ hs _ _ | twelve _ _ hs _ _ =>
    rw [extension_card hs]; norm_num [C4Square, E4, C, Nat.card_prod]
  | thirteen _ _ _ hs _ _ =>
    rw [extension_card hs, DihedralGroup.nat_card]
    norm_num [C4Square, C, Nat.card_prod]

/-- Every original or corrected F.6.18 source alternative bounds the common Sylow order. -/
theorem source_alternative_sylow_card_le {D : Type u} [Group D] [Finite D]
    {G₁ G₂ : Subgroup D} {S : Sylow 2 D} (r : SourceAlternative G₁ G₂ S) :
    Nat.card S ≤ 128 := by
  rcases r with (r | hr) | hr
  · exact alternative_sylow_bound r
  · obtain ⟨r⟩ := hr
    rw [Nat.card_congr r.sylow.some.toEquiv, DihedralGroup.nat_card]; norm_num
  · obtain ⟨r⟩ := hr
    rw [Nat.card_congr r.sylow.some.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
    norm_num [C]

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
