module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.OriginalGeometry
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# The actual rank-one row supplies its original block

The B.5 rank-one row first makes R Sylow in KR by the original-domain
C.2.7 geometry. The proved rank-one block theorem then gives the concrete
L2-even or A5 block on K. Its solvable A3 case is excluded by the original
C-component hypothesis. All actions and quotient subgroups remain literal.

Source: Aschbacher–Smith C.2.7(3)(a), printed pp.145–147, and the rank-one
branches of 15.3.18–19, printed pp.1126–1127.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {H K R M : Subgroup G}

/-- The source component cannot be the solvable A₃ block among the χ₀ types. -/
theorem source_rankOne_blocks_of_sylow
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hs : Chapter1.IsSylowIn 2 R (K ⊔ R)) :
    (∃ n, IsL2EvenBlock K n) ∨ IsAlternatingBlock K 5 := by
  obtain ⟨_,hc⟩ := source_chiZero_of_sylow_input h hs
  rcases hc with hc | h3 | h5
  · exact Or.inl hc
  · obtain ⟨e⟩ := h3.equiv_alternatingFour
    let : Group.IsSolvable (alternatingGroup (Fin 4)) :=
      alternatingGroup_fin_four_isSolvable
    let : Group.IsSolvable K :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact (h.component.2.not_isSolvable
      (Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe h.component.1).toMonoidHom)
        (subgroupOfEquivOfLe h.component.1).injective)).elim
  · exact Or.inr h5

/-- The actual rank-one B.5 row supplies both the marked geometry and the
concrete original block used in 15.3.18--19. -/
theorem rankOne_row_blocks_from_source
    (h : Input KnownSimple.IsKnownSimple H R M K)
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
      IsRankOneBorel (starImage K R K) (starM K R M) ∧
      Chapter1.IsSylowIn 2 R (K ⊔ R) ∧
      ((∃ n, IsL2EvenBlock K n) ∨ IsAlternatingBlock K 5) := by
  obtain ⟨hj,hb,hs⟩ := rankOne_row_geometry_from_source h hCJ s F natural hratio hoff
  exact ⟨hj,hb,hs,source_rankOne_blocks_of_sylow h hs⟩
end CFSG.Quasithin.ChapterC.C27Source
