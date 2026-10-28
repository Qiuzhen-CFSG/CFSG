module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.Solvable
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SolvableCoordinates.WholeActor

/-!
# The full natural action of the solvable E.2.3 quotient

The earlier source produces the actual S₃ factors and original Sylow
transitivity. Minimal-parabolic offender generation puts the whole residual
in their product. Faithfulness of the actual centralizer quotient then
identifies the entire actor on the original moved space with SL₂(2) or O₄⁺(2).
No extra actor-order, centralizer, permutation-image or coordinates premise
is retained.

Source: Aschbacher–Smith E.2.3, pp.216–217; 13.2.8(3), p.880.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

/-- Whole-actor coordinates for the literal solvable reduced action image. -/
theorem solvable_whole_actor
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hcore : pCore 2 H = ⊥) (hsolv : Group.IsSolvable H)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hrank : primeRank 3 G ≤ 2) :
    ChapterB.SmallNaturalMovedAction (NormalElementaryQuotient.representation U q hq hker) := by
  let ρ := NormalElementaryQuotient.representation U q hq hker
  obtain ⟨d,hc,_,ht⟩ := solvable_factors T hP U q hq hker hcore hsolv hJ hrank
  have hne : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hker ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T : Subgroup G) ≤ ⊤)))
  have hp := (ChapterB.minimalParabolic_reduced_image T hP q hq hcore hne).2
  have hff : IsFFModule ρ := (isFFModule_iff_quadraticRatio_le_one ρ).mpr d.ratio_one.le
  have hr := (ChapterB.offender_generation (T.mapSurjective hq) hp ρ hff hcore).1
  apply d.toSolvableFFFactors.small_natural_moved_action
    (NormalElementaryQuotient.representation_injective U q hq hker) hcore hr hc
  intro i j
  obtain ⟨t,ht⟩ := ht i j
  exact ⟨q t,ht⟩

/-- The full original centralizer quotient, with its natural moved action. -/
theorem source_solvable_whole_actor
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hrank : primeRank 3 G ≤ 2)
    (hsolv : letI := hU.normal; Group.IsSolvable (G ⧸ centralizer (U : Set G))) :
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set G)
    let q := QuotientGroup.mk' C
    ChapterB.SmallNaturalMovedAction (NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)) := by
  let := hU.normal
  let := hU.elementary
  exact solvable_whole_actor T hP U _ (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) hU.quotient_pCore_eq_bot hsolv hJ hrank

end CFSG.Quasithin.ChapterE.ThompsonAction
