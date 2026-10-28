module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.Five
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.FlagTorus
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import Theory.SpecificGroups.HigherLinear.RadicalParabolics
public import Theory.NumberTheory.BinaryTorusParity

/-!
# Odd field degree in the original linear-three component

The actual C.2.7 radical has its normalizer in the original star intersection.
For an even-degree binary field, SL₃ has order above the small-model cutoff,
so the genuine radical flag theorem applies. Every resulting flag stabilizer
contains a split torus of order (q−1)², divisible by nine. This contradicts
the proved order bound on C_M(A)'s star image.

The final consumer keeps the full moved-section conclusion and imposes odd
field degree on both surviving linear-three action rows. The symmetric-five
row, the further field reductions, and the chief-factor contradiction remain
with this original-plane assembly owner.
Source: Aschbacher--Smith 13.3.12, pp.889--890, and C.2.7, pp.145--147.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource Representation Representation.BinaryOffender
universe u v w
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

/-- Even-degree SL₃ is excluded on the original star component. -/
theorem Context.not_even_linearThree_star (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J) (F : BinaryField) (heven : Even F.degree)
    (e : starImage J ((L ⊔ T).pCoreIn 2) J ≃* SL(3,F.Carrier)) : False := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let C := starImage J Q J
  let U := (starImage J Q Q).subgroupOf C
  let P := (starM J Q (centralizer (d.A : Set G) ⊓ normalizer (L : Set G))).subgroupOf C
  have hq : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    have hn : 2 ≤ F.degree := by have := F.degree_pos; obtain ⟨n,hn⟩ := heven; omega
    exact (show 2^2 ≤ 2^F.degree from pow_le_pow_right₀ (by decide) hn)
  have hlarge : 40320 < Nat.card C := by
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
    have hh : 4^3*(4^3-1)*(4^2-1) ≤
        Nat.card F.Carrier ^ 3 * (Nat.card F.Carrier ^ 3 - 1) *
          (Nat.card F.Carrier ^ 2 - 1) := by gcongr
    norm_num at hh
    omega
  obtain ⟨hU,hP⟩ := ChapterC.C27Source.star_intersection_placement_from_source_of_large_order
    j.input hlarge
  obtain ⟨k,W,hk,hm,hp,hw⟩ := Matrix.HigherLinear.radical_normalizer_eq_partialFlag_three
    (U.map e.toMonoidHom) (hU.map_equiv e)
  have hthree : 3 ∣ Nat.card F.Carrier - 1 := by
    rw [F.card_eq]
    exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff F.degree).mpr heven
  have h9 : 9 ∣ Nat.card (normalizer (U.map e.toMonoidHom : Set SL(3,F.Carrier))) := by
    rw [hw]
    exact Matrix.PSL3.LinearThree.FlagTorus.nine_dvd_partialFlag W hk hm hp hthree
  have hle : normalizer (U.map e.toMonoidHom : Set SL(3,F.Carrier)) ≤ P.map e.toMonoidHom := by
    rw [← map_equiv_normalizer_eq]
    exact map_mono hP
  have hd := h9.trans (card_dvd_of_le hle)
  rw [card_map_of_injective e.injective] at hd
  change 9 ∣ Nat.card ((starM J Q
    (centralizer (d.A : Set G) ⊓ normalizer (L : Set G))).subgroupOf C) at hd
  rw [Nat.card_congr (subgroupOfEquivOfLe (starM_le J Q
      (centralizer (d.A : Set G) ⊓ normalizer (L : Set G)))).toEquiv] at hd
  exact s.plane_starM_nine_not_dvd d J hd

/-- Every actual linear-three star model has odd field degree. -/
theorem Context.linearThree_star_odd (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J) (F : BinaryField)
    (e : starImage J ((L ⊔ T).pCoreIn 2) J ≃* SL(3,F.Carrier)) : Odd F.degree := by
  exact Nat.not_even_iff_odd.mp (fun h => s.not_even_linearThree_star d J j F h e)

section Actions
variable {D : Type v} [Group D] {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)

/-- Original higher action markings after the field-parity exclusion. -/
inductive PlaneOddHigherActionCase (K : Subgroup D) (c : MovedSection ρ K) : Prop
  | linearThree (F : BinaryField) (odd : Odd F.degree)
      (e : ActionEquiv (c.action.comp K.subtype) (linearNatural F 3))
  | doubleThree (F : BinaryField) (odd : Odd F.degree)
      (e : ActionEquiv (c.space.toRepresentation.comp K.subtype)
        (repeated (linearNatural F 3) 2))
  | symmetricFive
      (e : MarkedActionEquiv c.action (offenderSubgroup c.action) K
        (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))
end Actions

/-- Apply the field bound to the same full moved section and original component. -/
theorem Context.even_block_or_odd_higher_action
    (s : Context T L V) (d : MarkedPlane V) (J : Subgroup G) (j : LocalData T L d J) :
    let ρ := starRepresentation J ((L ⊔ T).pCoreIn 2)
    let B := offenderSubgroup ρ
    let K := (starImage J ((L ⊔ T).pCoreIn 2) J).subgroupOf B
    (Chapter1.IsSylowIn 2 ((L ⊔ T).pCoreIn 2) (J ⊔ (L ⊔ T).pCoreIn 2) ∧
      IsRankOneBorel (starImage J ((L ⊔ T).pCoreIn 2) J)
        (starM J ((L ⊔ T).pCoreIn 2)
          (centralizer (d.A : Set G) ⊓ normalizer (L : Set G))) ∧
      ∃ n, ChapterC.IsL2EvenBlock J n) ∨
    ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp B.subtype) K,
      PlaneOddHigherActionCase (ρ.comp B.subtype) K c.sectionData := by
  rcases s.even_block_or_higher_action d J j with hb | ⟨c,hc⟩
  · exact Or.inl hb
  obtain ⟨hK,_⟩ := ChapterC.C27Source.star_moved_section_from_source j.input
  let e := (subgroupOfEquivOfLe hK).symm
  refine Or.inr ⟨c,?_⟩
  cases hc with
  | linearThree F a =>
    exact .linearThree F (s.linearThree_star_odd d J j F (e.trans a.groupEquiv)) a
  | doubleThree F a =>
    exact .doubleThree F (s.linearThree_star_odd d J j F (e.trans a.groupEquiv)) a
  | symmetricFive a => exact .symmetricFive a

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
