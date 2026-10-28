module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Ree.Obstructions

/-!
# Assembly from actual invariant local subgroups

Two subgroups generating L give the required overgroups after adjoining S.
The invariance contract uses N_S(L); it permits S to permute components.
If the first overgroup has order prime to three and every escaping short
subnormal subgroup of the second has a noncentral normal two-layer, the
block conclusion of 2.3.8(4) gives a contradiction.

This is a conditional reduction for Aschbacher–Smith 2.3.9(7), printed p.526.
It does not construct the Ree or Tits parabolics or assert their HeOver
membership. The model calculations must supply those facts and the layers.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree

open Subgroup ChapterC

variable {G : Type*} [Group G]

/-- The generating pair and its correct relative invariance requirement.
The model owner constructs the two subgroups as actual parabolics. -/
structure InvariantPair (L S : Subgroup G) where
  left : Subgroup L
  right : Subgroup L
  generate : left ⊔ right = ⊤
  invariant_left : S ⊓ normalizer (L : Set G) ≤
    normalizer (left.map L.subtype : Set G)
  invariant_right : S ⊓ normalizer (L : Set G) ≤
    normalizer (right.map L.subtype : Set G)

namespace InvariantPair

variable {L S : Subgroup G} (d : InvariantPair L S)

def leftOver : Subgroup G := d.left.map L.subtype ⊔ S

def rightOver : Subgroup G := d.right.map L.subtype ⊔ S

theorem leftOver_le : d.leftOver ≤ L ⊔ S :=
  sup_le_sup (map_subtype_le _) le_rfl

theorem rightOver_le : d.rightOver ≤ L ⊔ S :=
  sup_le_sup (map_subtype_le _) le_rfl

/-- Adjoining S preserves generation even when S permutes components. -/
theorem overgroups_generate : d.leftOver ⊔ d.rightOver = L ⊔ S := by
  have hg : d.left.map L.subtype ⊔ d.right.map L.subtype = L := by
    rw [← Subgroup.map_sup, d.generate, ← MonoidHom.range_eq_map, L.range_subtype]
  change (d.left.map L.subtype ⊔ S) ⊔ (d.right.map L.subtype ⊔ S) = L ⊔ S
  rw [sup_sup_sup_comm, sup_idem, hg]

end InvariantPair

/-- The source assembly remains conditional on the genuine local calculations.
No block exclusion or refined classification conclusion is a premise. -/
theorem false_of_pair_calculations {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z)
    (d : InvariantPair L ((S : Subgroup H).map H.subtype))
    (he₁ : d.leftOver ∈ Chapter1.HeOver G
      (((S : Subgroup H).map H.subtype : Subgroup G) : Set G))
    (he₂ : d.rightOver ∈ Chapter1.HeOver G
      (((S : Subgroup H).map H.subtype : Subgroup G) : Set G))
    (hthree : ¬ 3 ∣ Nat.card d.leftOver)
    (hlayers : ∀ B : Subgroup d.rightOver, IsBlock B →
      B.map d.rightOver.subtype =
        ⁅B.map d.rightOver.subtype,
          Stellmacher.elementaryAbelianMaxJ ((S : Subgroup H).map H.subtype)⁆ →
      ¬ B.map d.rightOver.subtype ≤ M → HasNoncentralTwoLayer B) : False := by
  have hg : L ≤ d.leftOver ⊔ d.rightOver :=
    d.overgroups_generate.symm ▸ le_sup_left
  rcases exists_escapingBlock_of_pair h.blocks h.outside hg
      d.leftOver_le d.rightOver_le he₁ he₂ with ⟨B, hb, _, _⟩ | ⟨B, hb, hout, hm⟩
  · exact not_chiZero_subgroup_of_three_free hthree B hb.2
  · exact not_short_of_noncentral_two_layer (hlayers B hb.1 hm hout) hb.1.short

/-- If the first overgroup already centralizes z, only the second local
characteristic-two calculation is needed for the contradiction. This version
is useful for the marked Tits endpoint. -/
theorem false_of_right_calculations {H L M : Subgroup G} {S : Sylow 2 H} {z : G}
    (h : LocalSetup H L M S z)
    (d : InvariantPair L ((S : Subgroup H).map H.subtype))
    (hleft : d.leftOver ≤ M)
    (he₂ : d.rightOver ∈ Chapter1.HeOver G
      (((S : Subgroup H).map H.subtype : Subgroup G) : Set G))
    (hlayers : ∀ B : Subgroup d.rightOver, IsBlock B →
      B.map d.rightOver.subtype =
        ⁅B.map d.rightOver.subtype,
          Stellmacher.elementaryAbelianMaxJ ((S : Subgroup H).map H.subtype)⁆ →
      ¬ B.map d.rightOver.subtype ≤ M → HasNoncentralTwoLayer B) : False := by
  have hout : ¬ d.rightOver ≤ M := by
    intro hright
    apply h.outside
    have hg : L ≤ d.leftOver ⊔ d.rightOver :=
      d.overgroups_generate.symm ▸ le_sup_left
    exact hg.trans (sup_le hleft hright)
  obtain ⟨decomposition⟩ := h.blocks d.rightOver d.rightOver_le he₂ hout
  obtain ⟨B, hb, hBM, hm⟩ := decomposition.exists_escapingBlock hout
  exact not_short_of_noncentral_two_layer (hlayers B hb.1 hm hBM) hb.1.short

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Ree

end
