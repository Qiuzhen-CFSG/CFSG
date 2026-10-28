module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.SourceCount.Foundations

/-!
# Counting a disjoint subgroup family together with a marked subgroup

Nonidentity elements in distinct TI conjugates are distinct, and a subgroup
disjoint from all conjugates contributes its whole order. The resulting
injection is used both in normalizer growth and in the exact involution census.

Source: GLS4, Chapter 2, Lemma 15.6, opening and counting paragraphs.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion.SourceCount.Census
open Subgroup Theory.GroupTheory
universe u v
variable {G : Type u} [Group G] [Finite G]

public theorem card_nonidentity (H : Type*) [Group H] [Finite H] :
    Nat.card {x : H // x ≠ 1} = Nat.card H - 1 := by
  classical
  let := Fintype.ofFinite H
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]

omit [Finite G] in
public theorem family_union_injective {ι : Type v} (A W : Subgroup G)
    (F : ι → Subgroup G) (hAW : A ≤ W) (hFW : ∀ i, F i ≤ W)
    (hAF : ∀ i, Disjoint A (F i))
    (hFF : ∀ i j, i ≠ j → Disjoint (F i) (F j)) :
    Function.Injective (Sum.elim
      (fun a : A => (⟨a, hAW a.property⟩ : W))
      (fun p : Σ i, {x : F i // x ≠ 1} => ⟨p.2.val, hFW p.1 p.2.val.property⟩)) := by
  intro a b he
  have hv := congrArg Subtype.val he
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Subtype.ext hv)
    | inr b =>
      exact (b.2.property (Subtype.ext (disjoint_def.mp (hAF b.1)
        (hv ▸ a.property) b.2.val.property))).elim
  | inr a =>
    cases b with
    | inl b =>
      exact (a.2.property (Subtype.ext (disjoint_def.mp (hAF a.1)
        (hv.symm ▸ b.property) a.2.val.property))).elim
    | inr b =>
      have hi : a.1 = b.1 := by
        by_contra hn
        exact a.2.property (Subtype.ext (disjoint_def.mp (hFF a.1 b.1 hn)
          a.2.val.property (hv.symm ▸ b.2.val.property)))
      obtain ⟨i,a⟩ := a
      obtain ⟨j,b⟩ := b
      dsimp only at hi hv
      subst j
      exact congrArg Sum.inr (congrArg (Sigma.mk i) (Subtype.ext (Subtype.ext hv)))

public theorem family_union_card {ι : Type v} [Finite ι] (A W : Subgroup G)
    (F : ι → Subgroup G) (hAW : A ≤ W) (hFW : ∀ i, F i ≤ W)
    (hAF : ∀ i, Disjoint A (F i))
    (hFF : ∀ i j, i ≠ j → Disjoint (F i) (F j)) {r : ℕ}
    (hcard : ∀ i, Nat.card (F i) = r) :
    Nat.card A + Nat.card ι * (r - 1) ≤ Nat.card W := by
  classical
  let := Fintype.ofFinite ι
  have hc := Nat.card_le_card_of_injective _ (family_union_injective A W F hAW hFW hAF hFF)
  simpa only [Nat.card_sum, Nat.card_sigma, card_nonidentity, hcard,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card] using hc

end BenderSuzuki.ZD.LinearExclusion.SourceCount.Census
