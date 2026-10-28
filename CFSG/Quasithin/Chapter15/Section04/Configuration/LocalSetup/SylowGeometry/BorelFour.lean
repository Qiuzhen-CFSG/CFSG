module

public import Theory.SpecificGroups.SL2.BorelSmallInvariant
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear.MatrixBorel
public import CFSG.Quasithin.ChapterC.Section01.BlockDefs

/-!
# Borel restrictions on the four-group in the even-field cases

These adapters supply the concrete calculations in the two even-field cases
of Aschbacher–Smith 15.4.20, `refs/quasithin.pdf`, printed p.1164. The Borel
is the actual upper triangular subgroup from Chapter F, identified with the
normalizer of `upperUnipotent`. It and its two-factor product are two-perfect.
A normalized four-group lying in the root group or its two-factor product
forces the field order to be at most four.

The natural-module bounds concern arbitrary additive subgroups. For a block,
`BlockModuleModel` supplies the actual quotient and module isomorphisms and
intertwines conjugation with matrix multiplication. Each Borel matrix is
lifted to the supplied acting subgroup, so its invariant subgroup has an
invariant image in the natural module. That image has cardinality at least
|F| and at most the original subgroup's cardinality.

The block adapters require both a nontrivial image in U/C_U(L) and an actual
acting subgroup whose image contains the Borel (or product Borel). These
placement and projection hypotheses are inputs to the source assembly.
-/

@[expose] public section

open Matrix
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup
open SpecialLinearGroup BenderSuzuki.Converse ChapterC
variable {F : Type*} [Field F]

/-- Identify the root normalizer with the Borel used by the Chapter F matrix API. -/
theorem rankOneBorel_eq_sourceBorel : rankOneBorel F = Borel F := by
  change Subgroup.normalizer (upperUnipotent F : Set (SL(2, F))) = Borel F
  rw [← ChapterF.Source.Linear.unip_eq_upper, ChapterF.Source.Linear.unip_normalizer]

theorem linear_borel_isPPerfect [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F) :
    IsPPerfect 2 (Borel F) := by
  rw [← rankOneBorel_eq_sourceBorel]
  exact rankOneBorel_isPPerfect hq

theorem linear_borel_pair_isPPerfect [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F) :
    IsPPerfect 2 ((Borel F).prod (Borel F)) := by
  have hp : IsPPerfect 2 ((Borel F) × (Borel F)) := by
    rw [← rankOneBorel_eq_sourceBorel]
    exact rankOneBorel_prod_isPPerfect hq
  exact hp.of_surjective (Subgroup.prodEquiv (Borel F) (Borel F)).symm.toMonoidHom
    (Subgroup.prodEquiv (Borel F) (Borel F)).symm.surjective

theorem linear_root_eq_of_borel_normalized [Finite F] [CharP F 2]
    (W : Subgroup (SL(2, F))) (hWU : W ≤ upperUnipotent F) (hne : W ≠ ⊥)
    (hn : Borel F ≤ Subgroup.normalizer (W : Set _)) : W = upperUnipotent F := by
  apply eq_upperUnipotent_of_normalized W hWU hne
  rwa [rankOneBorel_eq_sourceBorel]

theorem linear_root_four_field_bound [Finite F] [CharP F 2]
    (W : Subgroup (SL(2, F))) (hWU : W ≤ upperUnipotent F) (hcard : Nat.card W = 4)
    (hn : Borel F ≤ Subgroup.normalizer (W : Set _)) : Nat.card F ≤ 4 := by
  have hne : W ≠ ⊥ := by intro h; subst W; simp at hcard
  have he := linear_root_eq_of_borel_normalized W hWU hne hn
  rw [he, card_upperUnipotent] at hcard
  exact hcard.le

theorem linear_root_pair_four_field_bound [Finite F] [CharP F 2]
    (W : Subgroup (SL(2, F) × SL(2, F)))
    (hWU : W ≤ (upperUnipotent F).prod (upperUnipotent F)) (hcard : Nat.card W = 4)
    (hn : (Borel F).prod (Borel F) ≤ Subgroup.normalizer (W : Set _)) : Nat.card F ≤ 4 := by
  have hne : W ≠ ⊥ := by intro h; subst W; simp at hcard
  rw [← rankOneBorel_eq_sourceBorel] at hn
  exact hcard ▸ card_le_of_root_prod_normalized W hWU hne hn

theorem linear_natural_four_field_bound [Finite F]
    (W : AddSubgroup (Fin 2 → F)) (hcard : Nat.card W = 4)
    (hinv : ∀ g ∈ Borel F, ∀ v ∈ W, g.val *ᵥ v ∈ W) : Nat.card F ≤ 4 := by
  have hne : W ≠ ⊥ := by intro h; subst W; simp at hcard
  rw [← rankOneBorel_eq_sourceBorel] at hinv
  exact hcard ▸ card_le_of_natural_borel_invariant W hne hinv

theorem linear_natural_pair_four_field_bound [Finite F]
    (W : AddSubgroup ((Fin 2 → F) × (Fin 2 → F))) (hcard : Nat.card W = 4)
    (hinv : ∀ g ∈ (Borel F).prod (Borel F), ∀ v ∈ W,
      (g.1.val *ᵥ v.1, g.2.val *ᵥ v.2) ∈ W) : Nat.card F ≤ 4 := by
  have hne : W ≠ ⊥ := by intro h; subst W; simp at hcard
  rw [← rankOneBorel_eq_sourceBorel] at hinv
  exact hcard ▸ card_le_of_natural_pair_borel_invariant W hne hinv

private theorem blockModel_card_bound {L A V : Type*} [Group L] [Finite L]
    [Group A] [Group V] {ρ : A →* MulAut V}
    (model : BlockModuleModel L ρ) (B : Subgroup A) (k : ℕ)
    (hbound : ∀ W : Subgroup V, W ≠ ⊥ →
      (∀ b ∈ B, ∀ v ∈ W, ρ b v ∈ W) → k ≤ Nat.card W)
    (W : Subgroup (blockU L))
    (himage : W.map (QuotientGroup.mk' (blockFixed L)) ≠ ⊥)
    (H : Subgroup L)
    (hcover : B ≤ H.map (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))
    (hinv : ∀ l ∈ H, ∀ u ∈ W, blockConjugate L l u ∈ W) : k ≤ Nat.card W := by
  let π := QuotientGroup.mk' (blockFixed L)
  let Wm := (W.map π).map model.moduleIso.toMonoidHom
  have hne : Wm ≠ ⊥ := by
    intro h
    exact himage ((Subgroup.map_eq_bot_iff_of_injective (W.map π) model.moduleIso.injective).mp h)
  have hact : ∀ b ∈ B, ∀ v ∈ Wm, ρ b v ∈ Wm := by
    intro b hb v hv
    obtain ⟨l, hl, ha⟩ := hcover hb
    change model.quotientIso (QuotientGroup.mk' (pCore 2 L) l) = b at ha
    obtain ⟨w, hw, rfl⟩ := hv
    obtain ⟨u, hu, rfl⟩ := hw
    refine ⟨π (blockConjugate L l u), ⟨blockConjugate L l u, hinv l hl u hu, rfl⟩, ?_⟩
    change model.moduleIso (QuotientGroup.mk' (blockFixed L) (blockConjugate L l u)) =
      ρ b (model.moduleIso (QuotientGroup.mk' (blockFixed L) u))
    exact (model.intertwining l u).trans (by rw [ha])
  calc
    k ≤ Nat.card Wm := hbound Wm hne hact
    _ = Nat.card (W.map π) := Subgroup.card_map_of_injective model.moduleIso.injective
    _ ≤ Nat.card W := Nat.card_image_le (Set.toFinite _)

/-- Transfer the natural-plane bound through an actual block module model. -/
theorem linear_block_invariant_card_bound {L : Type*} [Group L] [Finite L] [Finite F]
    (model : BlockModuleModel L (Matrix.SL2.naturalAction F))
    (W : Subgroup (blockU L))
    (himage : W.map (QuotientGroup.mk' (blockFixed L)) ≠ ⊥)
    (H : Subgroup L)
    (hcover : Borel F ≤ H.map
      (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))
    (hinv : ∀ l ∈ H, ∀ u ∈ W, blockConjugate L l u ∈ W) : Nat.card F ≤ Nat.card W := by
  apply blockModel_card_bound model (Borel F) (Nat.card F) ?_ W himage H hcover hinv
  intro V hne hV
  rw [← rankOneBorel_eq_sourceBorel] at hV
  exact Matrix.SL2.card_le_of_naturalAction_borel_invariant V hne hV

/-- Transfer the two independent natural-plane actions through a block module model. -/
theorem linear_block_pair_invariant_card_bound {L : Type*} [Group L] [Finite L] [Finite F]
    (model : BlockModuleModel L (Matrix.SL2.naturalPairAction F))
    (W : Subgroup (blockU L))
    (himage : W.map (QuotientGroup.mk' (blockFixed L)) ≠ ⊥)
    (H : Subgroup L)
    (hcover : (Borel F).prod (Borel F) ≤ H.map
      (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))
    (hinv : ∀ l ∈ H, ∀ u ∈ W, blockConjugate L l u ∈ W) :
    Nat.card F ≤ Nat.card W := by
  apply blockModel_card_bound model ((Borel F).prod (Borel F)) (Nat.card F) ?_ W himage H hcover hinv
  intro V hne hV
  rw [← rankOneBorel_eq_sourceBorel] at hV
  exact Matrix.SL2.card_le_of_naturalPairAction_borel_invariant V hne hV

/-- A four-subgroup with nonzero module image forces the field order to be at most four. -/
theorem linear_block_four_field_bound {L : Type*} [Group L] [Finite L] [Finite F]
    (model : BlockModuleModel L (Matrix.SL2.naturalAction F))
    (W : Subgroup (blockU L)) (hcard : Nat.card W = 4)
    (himage : W.map (QuotientGroup.mk' (blockFixed L)) ≠ ⊥)
    (H : Subgroup L)
    (hcover : Borel F ≤ H.map
      (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))
    (hinv : ∀ l ∈ H, ∀ u ∈ W, blockConjugate L l u ∈ W) : Nat.card F ≤ 4 :=
  hcard ▸ linear_block_invariant_card_bound model W himage H hcover hinv

/-- The same obstruction for two independently acted-on natural planes. -/
theorem linear_block_pair_four_field_bound {L : Type*} [Group L] [Finite L] [Finite F]
    (model : BlockModuleModel L (Matrix.SL2.naturalPairAction F))
    (W : Subgroup (blockU L)) (hcard : Nat.card W = 4)
    (himage : W.map (QuotientGroup.mk' (blockFixed L)) ≠ ⊥)
    (H : Subgroup L)
    (hcover : (Borel F).prod (Borel F) ≤ H.map
      (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))
    (hinv : ∀ l ∈ H, ∀ u ∈ W, blockConjugate L l u ∈ W) : Nat.card F ≤ 4 :=
  hcard ▸ linear_block_pair_invariant_card_bound model W himage H hcover hinv

end CFSG.Quasithin.Chapter15.Section04.LocalSetup
