module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.OriginalRestriction
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.RankOneSylow
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SymplecticSource


/-!
# Original-domain C.2.7 geometry wrappers

The source input only normalizes the component by the radical.  Restricting to
`K ⊔ R` makes `K` normal by an actual subgroup construction; the relative
radical identity then transports C.2.7(1)--(2), the B.5 moved section, and the
Thompson/rank-one/symplectic placement endpoints back to the original `H`, `M`.
The marked subgroup is kept as `starM K R M`; no ambient-normality or model
premise is added.  C.2.7(3)'s remaining Asc81b/C.1.32 classification is not
asserted by this file.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H K R M : Subgroup G}

omit [Finite G] in
theorem starM_inter_join (K R M : Subgroup G) :
    starM K R (M ⊓ (K ⊔ R)) = starM K R M := by
  unfold starM
  congr 1
  exact inf_assoc M (K ⊔ R) K |>.trans (congrArg (M ⊓ ·) (inf_eq_right.mpr le_sup_left))

theorem star_thompson_intersection_from_source (h : Input κ H R M K) :
    starImage K R K ⊓ normalizer
        (starImage K R (elementaryAbelianMaxJ R) : Set (StarQuotient K R)) ≤ starM K R M ∧
      starM K R M < starImage K R K := by
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  simpa only [starM_inter_join] using star_thompson_intersection_of_normal_input (source_join_input h)

theorem star_intersection_normalizer_core_from_source (h : Input κ H R M K) :
    (normalizer ((starImage K R R).subgroupOf (starImage K R K) : Set (starImage K R K))).pCoreIn 2 =
      (starImage K R R).subgroupOf (starImage K R K) := by
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  exact star_intersection_normalizer_core_of_normal_input (source_join_input h)

theorem star_intersection_radical_from_source (h : Input κ H R M K)
    (hne : (starImage K R R).subgroupOf (starImage K R K) ≠ ⊥) :
    IsPRadical 2 ((starImage K R R).subgroupOf (starImage K R K)) :=
  ⟨hne,star_intersection_normalizer_core_from_source h⟩

theorem rankOne_row_geometry_from_source
    (h : Input κ H R M K)
    (hCJ : starImage K R K ≤ offenderSubgroup (starRepresentation K R))
    (s : MovedSection ((starRepresentation K R).comp (offenderSubgroup (starRepresentation K R)).subtype)
      ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))))
    (F : BinaryField)
    (natural : ActionEquiv
      (s.action.comp ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))).subtype)
      (linearNatural F 2))
    (hratio : quadraticRatio s.action = 1)
    (hoff : ∀ B, IsBestOffender s.action B →
      ∃ S : Sylow 2 ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))),
        B = (S : Subgroup _).map
          ((starImage K R K).subgroupOf (offenderSubgroup (starRepresentation K R))).subtype) :
    Chapter1.IsSylowIn 2 (starImage K R (elementaryAbelianMaxJ R)) (starImage K R K) ∧
      IsRankOneBorel (starImage K R K) (starM K R M) ∧ Chapter1.IsSylowIn 2 R (K ⊔ R) := by
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  simpa only [starM_inter_join] using
    rankOne_row_geometry (source_join_input h) hCJ s F natural hratio hoff


theorem star_thompson_le_offenderSubgroup_from_source
    (h : Input κ H R M K) :
    starImage K R (elementaryAbelianMaxJ R) ≤ offenderSubgroup (starRepresentation K R) := by
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  exact star_thompson_le_offenderSubgroup (source_join_input h)

theorem star_intersection_placement_from_source_of_large_order
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hlarge : 40320 < Nat.card (starImage K R K)) :
    IsPRadical 2 ((starImage K R R).subgroupOf (starImage K R K)) ∧
      normalizer ((starImage K R R).subgroupOf (starImage K R K) :
          Set (starImage K R K)) ≤
        (starM K R M).subgroupOf (starImage K R K) := by
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  simpa only [starM_inter_join] using
    star_intersection_placement_of_large_order (source_join_input h) hlarge

open Theory.SpecificGroups.SymplecticFour

theorem star_symplectic_parabolic_or_chiZero_from_source
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (e : starImage K R K ≃* Sp F) (hq : 4 ≤ Nat.card F) :
    (∃ g : Sp F,
      (((starM K R M).subgroupOf (starImage K R K)).map e.toMonoidHom).map
          (MulAut.conj g).toMonoidHom = pointParabolic ∨
      (((starM K R M).subgroupOf (starImage K R K)).map e.toMonoidHom).map
          (MulAut.conj g).toMonoidHom = planeParabolic) ∨
      IsBlock (K.subgroupOf H) ∧ IsChiZeroBlock K := by
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  rcases star_symplectic_marked_parabolic_or_chiZero (source_join_input h) e hq with hp | hb
  · exact Or.inl (by simpa only [starM_inter_join] using hp)
  · have hs : IsShort K := hb.2.chi.short
    exact Or.inr ⟨⟨inferInstance,RankOne.Solvable.isShort_of_equiv
      (subgroupOfEquivOfLe h.component.1).symm hs,h.component.2.subnormal⟩,hb.2⟩


end CFSG.Quasithin.ChapterC.C27Source
