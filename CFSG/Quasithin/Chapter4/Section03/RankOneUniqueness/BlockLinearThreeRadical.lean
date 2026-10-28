module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesPreparation
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.LargeComponentPlacement
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow

/-!
# The actual radical intersection in the full SL₃ block quotient

The full SL₃(q) quotient has order greater than 40320 for every q = 2ⁿ
with n > 1, including q = 4. Thus the proved large-component placement
applies directly to the literal C.2.7 source extracted from the original
configuration. It gives radicality of the original star intersection and
places its entire normalizer in the actual local intersection.

No projective central quotient is substituted, and no parabolic placement
is assumed. Identifying this normalizer and its perfect L-subgroup with a
concrete parabolic and its solvable residual remains a separate model step.
Source: Aschbacher--Smith C.4.1(3), C.4.4--7, printed pp.151--153.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open ChapterC Chapter1.RadicalExclusions.ModelReduction
open FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem SourceConfiguration.block_linearThree_star_card
    (c : SourceConfiguration T L) {n : ℕ} (hn : 1 < n)
    (hb : IsBlock c.K) (hlinear : IsSL3EvenBlock c.K n) :
    40320 < Nat.card
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)) := by
  obtain ⟨_,_,F,_,_,hF,hmodel⟩ := hlinear
  obtain ⟨e⟩ := hmodel.quotient_iso
  rw [← Nat.card_congr (c.block_star_quotientEquiv hb).toEquiv,
    Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
  have hq : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
  have h3 : 64 ≤ Nat.card F ^ 3 := by
    simpa using Nat.pow_le_pow_left hq 3
  have h2 : 16 ≤ Nat.card F ^ 2 := by
    simpa using Nat.pow_le_pow_left hq 2
  have hm := Nat.mul_le_mul
    (Nat.mul_le_mul h3 (Nat.sub_le_sub_right h3 1)) (Nat.sub_le_sub_right h2 1)
  exact lt_of_lt_of_le (by norm_num : 40320 < 64 * (64 - 1) * (16 - 1)) hm

/-- The full SL₃ order is already large enough over F₄. The original
radical intersection is therefore nontrivial radical, and its full
normalizer lies in the actual local intersection. -/
theorem SourceConfiguration.block_linearThree_radical_placement
    (c : SourceConfiguration T L) {n : ℕ} (hn : 1 < n)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (hb : IsBlock c.K) (hlinear : IsSL3EvenBlock c.K n) :
    IsPRadical 2
      ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.I.pCoreIn 2)).subgroupOf
        (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype))) ∧
      normalizer
        (((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.I.pCoreIn 2)).subgroupOf
          (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype))) :
          Set (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype))) ≤
        (starM (c.K.map c.H.subtype) (c.I.pCoreIn 2)
          (c.H ⊓ normalizer (L : Set G))).subgroupOf
            (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)) := by
  have he : (c.K.map c.H.subtype).subgroupOf c.H = c.K :=
    c.K.comap_map_eq_self_of_injective c.H.subtype_injective
  let : ((c.K.map c.H.subtype).subgroupOf c.H).Normal := he.symm ▸ c.component_normal
  exact C27Source.star_intersection_placement_of_large_order (c.block_source_input hf)
    (c.block_linearThree_star_card hn hb hlinear)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
