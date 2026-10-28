module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericCartan
public import CFSG.Quasithin.ChapterF.Section01.SourceFaithfulTriple
public import Theory.GroupTheory.TwoLocalCoreObstruction

/-!
# The actual local pair in the normalized branch of 5.2.3

The source uses S = O₂(N_G(L) ∩ H), not the whole ambient Sylow T.
Its second local factor is initially L₂ ≤ O²(H); equality with O²(H)
belongs to the later Green Book argument. `Preparation` records the earlier
local obligations, without assuming a faithful amalgam or a global model.

Uniqueness over L and escape of L₂ kill the two-core of the generated
subgroup. The two Borel products then give cross-normalization, the literal
parabolics and the whole overlap. The genuine F.1.1 theorem supplies
faithfulness inside that generated subgroup. Constructing `Preparation`
from the Chapter 12 hypotheses and recognizing the resulting completion
remain separate source obligations.

Source: Aschbacher--Smith, 5.1.9--11 and 5.2.4--5, printed pp.634--635,
649--650; F.1.1 and F.1.3--9, printed pp.259--262 (`refs/quasithin.pdf`).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original intersection M_H, with M = N_G(L). -/
abbrev intersection (L H : Subgroup G) : Subgroup G := normalizer (L : Set G) ⊓ H

/-- The embedded intrinsic two-core used in 5.1.11 and 5.2.4. -/
abbrev sourceS (L H : Subgroup G) : Subgroup G :=
  (pCore 2 (intersection L H)).map (intersection L H).subtype

omit [Finite G] in
/-- The core lies in the literal T, since T is Sylow in the intersection. -/
theorem sourceS_le_sylow {T : Sylow 2 G} {L H : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) : sourceS L H ≤ (T : Subgroup G) := by
  have hT : (T : Subgroup G) ≤ intersection L H := le_inf hTL hTH
  have hc := Subgroup.map_mono
    (pCore_isPGroup.le_sylow_of_normal (T.subtype hT))
    (f := (intersection L H).subtype)
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hT] using hc

omit [Finite G] in
/-- Relative normality is retained: the intersection normalizes its core. -/
theorem intersection_normalizes_sourceS (L H : Subgroup G) :
    intersection L H ≤ normalizer (sourceS L H : Set G) := by
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
    (pCore 2 (intersection L H)).le_normalizer_map (intersection L H).subtype

/-- The earlier source obligations for the actual rank-one pair. In particular
the generated two-core, amalgam faithfulness and global recognition are not
fields. `unique_left` is the precise 4.3.2 input used by 5.2.5. -/
structure Preparation (T : Sylow 2 G) (L H A B L₂ : Subgroup G) : Prop where
  cartans : CartanPair T L H A B
  right_le_residual : L₂ ≤ residual H
  right_outside : ¬ L₂ ≤ normalizer (L : Set G)
  unique_left : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
    X = normalizer (L : Set G)
  left_intersection : sourceS L H ⊓ L = (T : Subgroup G) ⊓ L
  sylow : ∀ i : Fin 2, ∃ P : Sylow 2 (![L, L₂] i),
    (P : Subgroup (![L, L₂] i)).map (![L, L₂] i).subtype =
      sourceS L H ⊓ ![L, L₂] i
  right_quotient : ChapterF.Source.IsRankOneModel (L₂ ⧸ pCore 2 L₂)
  S_normalizes_right : sourceS L H ≤ normalizer (L₂ : Set G)
  cartan_normalizes_right : A ≤ normalizer (L₂ : Set G)
  right_borel : ChapterF.Source.borel L₂ (sourceS L H) =
    (sourceS L H ⊓ L₂) ⊔ (B ⊓ L₂)
  characteristic_two : ∀ i : Fin 2,
    generalizedFitting (ChapterF.Source.parabolic ![L, L₂] (sourceS L H) i) =
      pCore 2 (ChapterF.Source.parabolic ![L, L₂] (sourceS L H) i)

variable {T : Sylow 2 G} {L H A B L₂ W : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B L₂)
include d

/-- Source 5.2.5, conditional only on its earlier uniqueness and escape inputs. -/
theorem Preparation.generated_twoCore_eq_bot :
    pCore 2 (ChapterF.Source.generated ![L, L₂] (sourceS L H)) = ⊥ := by
  by_contra hc
  obtain ⟨X, hX, hgen⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot
    (ChapterF.Source.generated ![L, L₂] (sourceS L H)) hc
  have he : X = normalizer (L : Set G) :=
    d.unique_left X hX ((le_sup_left.trans le_sup_left).trans hgen)
  exact d.right_outside (he ▸ (le_sup_right.trans le_sup_left).trans hgen)

omit [Finite G] in
/-- The left Borel is computed with S, but is exactly the original N_L(T∩L). -/
theorem Preparation.left_borel_eq :
    ChapterF.Source.borel L (sourceS L H) = localBorel T L := by
  unfold ChapterF.Source.borel localBorel
  rw [d.left_intersection]

/-- The source odd Cartan supplements S∩L in the left Borel. -/
theorem Preparation.left_borel_product
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ChapterF.Source.borel L (sourceS L H) = (sourceS L H ⊓ L) ⊔ A := by
  rw [d.left_borel_eq, d.left_intersection, d.cartans.left_sup_intersection hTL]

/-- Assemble all six genuine F.1.1 clauses from the original local inputs.
The quotient for the left factor comes from the original PSL₂(2ⁿ) witness. -/
theorem Preparation.hypothesisF11 {κ : GroupClass.{u}}
    (h : Input κ T L W n) (hTH : (T : Subgroup G) ≤ H) :
    ChapterF.Source.HypothesisF11 ![L, L₂] (sourceS L H) := by
  have hSL : sourceS L H ≤ normalizer (L : Set G) :=
    (sourceS_le_sylow h.sylow_normalizes hTH).trans h.sylow_normalizes
  refine ⟨inferInstance, pCore_isPGroup.map _, ?_, d.sylow, ?_, ?_,
    d.generated_twoCore_eq_bot, d.characteristic_two⟩
  · intro i
    fin_cases i
    · exact hSL
    · exact d.S_normalizes_right
  · intro i
    fin_cases i
    · exact .linear n (lt_trans (by decide) h.exponent) h.linear
    · exact d.right_quotient
  · intro i
    fin_cases i
    · change ChapterF.Source.borel L₂ (sourceS L H) ≤ normalizer (L : Set G)
      rw [d.right_borel]
      exact sup_le (inf_le_left.trans hSL)
        (inf_le_left.trans (d.cartans.right_le.trans inf_le_left))
    · change ChapterF.Source.borel L (sourceS L H) ≤ normalizer (L₂ : Set G)
      rw [d.left_borel_product h.sylow_normalizes]
      exact sup_le (inf_le_left.trans d.S_normalizes_right) d.cartan_normalizes_right

omit [Finite G] in
/-- The first parabolic is literally L S (B∩L₂). -/
theorem Preparation.parabolic_zero :
    ChapterF.Source.parabolic ![L, L₂] (sourceS L H) 0 =
      L ⊔ sourceS L H ⊔ (B ⊓ L₂) := by
  change L ⊔ sourceS L H ⊔ ChapterF.Source.borel L₂ (sourceS L H) = _
  rw [d.right_borel]
  exact le_antisymm
    (sup_le le_sup_left (sup_le (inf_le_left.trans (le_sup_right.trans le_sup_left))
      le_sup_right))
    (sup_le le_sup_left (le_sup_right.trans le_sup_right))

/-- The second parabolic is literally L₂ S A. -/
theorem Preparation.parabolic_one
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ChapterF.Source.parabolic ![L, L₂] (sourceS L H) 1 =
      L₂ ⊔ sourceS L H ⊔ A := by
  change L₂ ⊔ sourceS L H ⊔ ChapterF.Source.borel L (sourceS L H) = _
  rw [d.left_borel_product hTL]
  exact le_antisymm
    (sup_le le_sup_left (sup_le (inf_le_left.trans (le_sup_right.trans le_sup_left))
      le_sup_right))
    (sup_le le_sup_left (le_sup_right.trans le_sup_right))

/-- The complete overlap retains the odd Cartans; it is not identified with S. -/
theorem Preparation.commonBorel_eq
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ChapterF.Source.commonBorel ![L, L₂] (sourceS L H) =
      sourceS L H ⊔ A ⊔ (B ⊓ L₂) := by
  change ChapterF.Source.borel L (sourceS L H) ⊔
    ChapterF.Source.borel L₂ (sourceS L H) ⊔ sourceS L H = _
  rw [d.left_borel_product hTL, d.right_borel]
  apply le_antisymm
  · exact sup_le
      (sup_le
        (sup_le (inf_le_left.trans (le_sup_left.trans le_sup_left))
          (le_sup_right.trans le_sup_left))
        (sup_le (inf_le_left.trans (le_sup_left.trans le_sup_left)) le_sup_right))
      (le_sup_left.trans le_sup_left)
  · exact sup_le
      (sup_le le_sup_right (le_sup_right.trans (le_sup_left.trans le_sup_left)))
      (le_sup_right.trans (le_sup_right.trans le_sup_left))

/-- The actual source parabolics intersect in S A (B∩L₂). -/
theorem Preparation.parabolic_intersection {κ : GroupClass.{u}}
    (h : Input κ T L W n) (hTH : (T : Subgroup G) ≤ H) :
    (L ⊔ sourceS L H ⊔ (B ⊓ L₂)) ⊓ (L₂ ⊔ sourceS L H ⊔ A) =
      sourceS L H ⊔ A ⊔ (B ⊓ L₂) := by
  rw [← d.parabolic_zero, ← d.parabolic_one h.sylow_normalizes,
    ChapterF.Source.lemma_F_1_3_6 (d.hypothesisF11 h hTH),
    d.commonBorel_eq h.sylow_normalizes]

/-- The finite faithful inclusion triple in the actual generated subgroup.
This invokes the genuine F.1.1 theory, not the legacy weak-BN-pair record. -/
theorem Preparation.faithfulTriple {κ : GroupClass.{u}}
    (h : Input κ T L W n) (hTH : (T : Subgroup G) ≤ H) :
    ChapterF.Source.LocallyRankOneTriple
      (fun i => (ChapterF.Source.parabolic ![L, L₂] (sourceS L H) i).subgroupOf
        (ChapterF.Source.generated ![L, L₂] (sourceS L H)))
      ((ChapterF.Source.commonBorel ![L, L₂] (sourceS L H)).subgroupOf
        (ChapterF.Source.generated ![L, L₂] (sourceS L H))) :=
  (d.hypothesisF11 h hTH).generatedLocallyRankOneTriple

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
