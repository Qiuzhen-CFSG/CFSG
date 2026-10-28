module

public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.LargeComponentPlacement
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SymplecticPlacement
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.Geometry

/-!
# Full marked placement for the large symplectic B.5 model

The actual Sp₄(q) carrier, q≥4, has order larger than 8!. The full B.5.1
source conclusion therefore puts every original best offender, and hence
J(R)*, in K*. Thompson heredity now places the radical-intersection normalizer
in the original M_K*, with no inner-action assumption on R*. The intrinsic
symplectic theorem identifies M_K* as a point or plane parabolic unless the
original component is a chi-zero block.

Source: Aschbacher--Smith C.2.7(3), pp.146--147, for the symplectic row of (!).
The remaining block and field restrictions belong to C.1.32.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {H K R M : Subgroup G}
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
private theorem symplectic_card_large (hq : 4 ≤ Nat.card F) : 40320 < Nat.card (Sp F) := by
  rw [card_sp]
  have hh := Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.pow_le_pow_left hq 4)
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1))
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 4) 1)
  exact lt_of_lt_of_le (by norm_num : 40320 < 4 ^ 4 * (4 ^ 2 - 1) * (4 ^ 4 - 1)) hh

omit [CharP F 2] in
theorem star_symplectic_radical_placement
    (h : Input KnownSimple.IsKnownSimple H R M K) [(K.subgroupOf H).Normal]
    (e : starImage K R K ≃* Sp F) (hq : 4 ≤ Nat.card F) :
    IsPRadical 2 ((starImage K R R).subgroupOf (starImage K R K)) ∧
      normalizer ((starImage K R R).subgroupOf (starImage K R K) :
          Set (starImage K R K)) ≤
        (starM K R M).subgroupOf (starImage K R K) := by
  apply star_intersection_placement_of_large_order h
  rw [Nat.card_congr e.toEquiv]
  exact symplectic_card_large hq

theorem star_symplectic_marked_parabolic_or_chiZero
    (h : Input KnownSimple.IsKnownSimple H R M K) [(K.subgroupOf H).Normal]
    (e : starImage K R K ≃* Sp F) (hq : 4 ≤ Nat.card F) :
    (∃ g : Sp F,
      (((starM K R M).subgroupOf (starImage K R K)).map e.toMonoidHom).map
          (MulAut.conj g).toMonoidHom = pointParabolic ∨
      (((starM K R M).subgroupOf (starImage K R K)).map e.toMonoidHom).map
          (MulAut.conj g).toMonoidHom = planeParabolic) ∨
      IsBlock (K.subgroupOf H) ∧ IsChiZeroBlock K := by
  apply star_symplectic_thompson_placement_or_chiZero h _ e
  apply star_thompson_le_component_of_large_order h
  rw [Nat.card_congr e.toEquiv]
  exact symplectic_card_large hq

/-- The exact existing parabolic predicate in C.2.7(3)(e), retaining the source chi-zero branch. -/
theorem star_sp4Four_parabolic_or_chiZero
    {F₄ : Type} [Field F₄] [Finite F₄] [CharP F₄ 2]
    (h : Input KnownSimple.IsKnownSimple H R M K) [(K.subgroupOf H).Normal]
    (e : starImage K R K ≃* Sp F₄) (hF : Nat.card F₄ = 4) :
    IsSp4FourMaximalParabolic ((starM K R M).subgroupOf (starImage K R K)) ∨
      IsBlock (K.subgroupOf H) ∧ IsChiZeroBlock K := by
  rcases star_symplectic_marked_parabolic_or_chiZero h e (by omega) with ⟨g,hg⟩ | hc
  · left
    refine ⟨F₄,inferInstance,inferInstance,hF,e.trans (MulAut.conj g),?_⟩
    have he : (e.trans (MulAut.conj g)).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by
      ext x
      rfl
    rw [he]
    simpa only [map_map] using hg
  · exact Or.inr hc

end CFSG.Quasithin.ChapterC.C27Source
