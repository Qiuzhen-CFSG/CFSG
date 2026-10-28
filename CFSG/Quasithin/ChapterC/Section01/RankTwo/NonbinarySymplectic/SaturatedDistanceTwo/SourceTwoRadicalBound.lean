module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoActorBound
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The full radical has cubic order in the large-movement branch

The component part has opposite image of order q, the fixed attachment has
opposite image of order at most 2q, and their join has index at most q in
the common radical. Normalized subgroup products therefore bound the full
opposite image by 2q³. Exact saturation permits only orders q³ and q⁴;
the original nonbinary hypothesis q > 2 excludes the latter.

All indices use the same full radical and the entire opposite core. The
marked-image and literal core-index conclusions preserve the original field
and its component projection. This supplies the Sylow exclusion in
Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*,
(3.7)(2), printed p.873. The subsequent point-radical contradiction remains.
-/

public noncomputable section
open Subgroup

private theorem index_le_three_factors
    {G : Type*} [Group G] [Finite G] (A B N : Subgroup G) [A.Normal] [N.Normal] :
    N.index ≤ (A ⊔ B).index * (N.relIndex A * N.relIndex B) := by
  let q := QuotientGroup.mk' N
  let : (A.map q).Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective N)
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes (A.map q) (B.map q)
    (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hp : 0 < Nat.card (A.map q ⊓ B.map q : Subgroup (G ⧸ N)) := Nat.card_pos
  have hs : N.relIndex (A ⊔ B) ≤ N.relIndex A * N.relIndex B := by
    rw [←QuotientGroup.ker_mk' N,relIndex_ker,relIndex_ker,relIndex_ker,Subgroup.map_sup]
    dsimp only [q] at hc hp
    nlinarith
  have ht : N.index ≤ (N ⊓ (A ⊔ B)).index := by
    have hh := relIndex_le_of_le_left (L := ⊤) (show N ⊓ (A ⊔ B) ≤ N from inf_le_left)
      (show (N ⊓ (A ⊔ B)).relIndex ⊤ ≠ 0 from index_ne_zero_of_finite)
    simpa only [relIndex_top_right] using hh
  have hm := relIndex_mul_index (H := N ⊓ (A ⊔ B)) (K := A ⊔ B) inf_le_right
  rw [inf_relIndex_right] at hm
  calc
    N.index ≤ (N ⊓ (A ⊔ B)).index := ht
    _ = N.relIndex (A ⊔ B) * (A ⊔ B).index := hm.symm
    _ ≤ (N.relIndex A * N.relIndex B) * (A ⊔ B).index := Nat.mul_le_mul_right _ hs
    _ = _ := Nat.mul_comm _ _

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The same full radical has opposite image of order at most 2q³. -/
theorem source_two_large_full_radical_index
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z)) :
    (Q d.radical z).relIndex (Q d.radical t) ≤ 2 * (2^n)^3 := by
  let := finite_stabilizer d.radical z
  let : Finite (Q d.radical t) := Finite.of_injective
    (inclusion c'.edge_le) (inclusion_injective _)
  let : ((componentRadical d a t).subgroupOf (Q d.radical t)).Normal :=
    normal_subgroupOf_of_le_normalizer c.componentRadical_normalized
  let : ((Q d.radical z).subgroupOf (Q d.radical t)).Normal := c'.core_normal
  have hAT : componentRadical d a t ≤ Q d.radical t := inf_le_left
  have hDT : fixedCore d.radical a ≤ Q d.radical t := inf_le_left.trans c.core_le_edge
  have hi := index_le_three_factors
    ((componentRadical d a t).subgroupOf (Q d.radical t))
    ((fixedCore d.radical a).subgroupOf (Q d.radical t))
    ((Q d.radical z).subgroupOf (Q d.radical t))
  rw [←subgroupOf_sup hAT hDT,relIndex_subgroupOf hAT,relIndex_subgroupOf hDT] at hi
  change (Q d.radical z).relIndex (Q d.radical t) ≤
    (componentRadical d a t ⊔ fixedCore d.radical a).relIndex (Q d.radical t) *
      ((Q d.radical z).relIndex (componentRadical d a t) *
        (Q d.radical z).relIndex (fixedCore d.radical a)) at hi
  have h₀ := (source_two_large_movement_images h d g hb hsat path hat hzt c c' hlarge).1
  have hD := source_two_large_fixedCore_actor_index h d g hb hsat path hat hzt c c' hlarge
  have hT := (componentRadical_fixedCore_relIndex h d g hb path.start_color c).2
  rw [h₀] at hi
  calc
    _ ≤ (componentRadical d a t ⊔ fixedCore d.radical a).relIndex (Q d.radical t) *
        (2^n * (Q d.radical z).relIndex (fixedCore d.radical a)) := hi
    _ ≤ 2^n * (2^n * (2 * 2^n)) := Nat.mul_le_mul hT (Nat.mul_le_mul_left _ hD)
    _ = _ := by ring

/-- Exact saturation and q > 2 force the original marked image to have order q³. -/
theorem source_two_large_marked_radical_card
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z)) :
    Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = (2^n)^3 := by
  have hm := source_two_large_full_radical_index h d g hb hsat path hat hzt c c' hlarge
  rw [relIndex,←c'.action_kernel,index_ker,c'.action_range] at hm
  rcases marked_radical_card h d g (by omega) hsat with hc | hc
  · simpa only [h.field_card] using hc
  rw [hc,h.field_card] at hm
  have hq : 2 < 2^n := by
    exact (show (2 : ℕ)^1 < 2^n from Nat.pow_lt_pow_right (by decide) h.nonbinary)
  have hp : 0 < (2^n)^3 := by positivity
  have hstrict : 2 * (2^n)^3 < (2^n)^4 := by
    rw [pow_succ]
    nlinarith
  omega

/-- The source cubic order is the literal full-radical/core index. -/
theorem source_two_large_full_radical_card
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z)) :
    (Q d.radical z).relIndex (Q d.radical t) = (2^n)^3 := by
  rw [relIndex,←c'.action_kernel,index_ker,c'.action_range]
  exact source_two_large_marked_radical_card h d g hb hsat path hat hzt c c' hlarge

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
