module

public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.WholeActor
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SolvableCoordinates.ResidualElementary
public import Theory.GroupTheory.ElementaryOddSylowUniqueMaximal
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Sylow maximality after the solvable reduced kernel is a two-group

The faithful solvable E.2.3 actor has elementary cubic two-residual.
Its unique maximal overgroup therefore forces the Sylow subgroup itself
to be maximal. If the original action kernel lies in the original Sylow,
subgroup correspondence lifts this maximality without changing either
the Sylow subgroup or the centralizer quotient.

Source: Aschbacher--Smith E.2.3 and the end of the proof on p.666 of 6.1.5.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
variable {G : Type*} [Group G] [Finite G]

/-- The solvable source actor has maximal Sylow whenever its actual
reduced-action kernel is contained in the original Sylow subgroup. -/
theorem sylow_isCoatom_of_solvable_reduced_kernel_le
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hrank : primeRank 3 G ≤ 2) (hsolv : Group.IsSolvable G)
    (hCT : centralizer (U : Set G) ≤ (T : Subgroup G)) :
    IsCoatom (T : Subgroup G) := by
  let := hU.normal
  let := hU.elementary
  let := hsolv
  let C := centralizer (U : Set G)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  let S := T.mapSurjective hq
  have hsmall := source_solvable_whole_actor T hP U hU hJ hrank inferInstance
  let : IsElementaryAbelian 3 (pResidual 2 (G ⧸ C)) := hsmall.wreath.residual_elementary
  have hne : q.ker ≠ ⊤ := by
    rw [QuotientGroup.ker_mk']
    intro he
    exact hJ (le_top.trans_eq he.symm)
  have hP' := (ChapterB.minimalParabolic_reduced_image T hP q hq
    hU.quotient_pCore_eq_bot hne).2
  have hmax := sylow_isCoatom_of_elementary_odd_supplement_unique_maximal
    (pResidual 2 (G ⧸ C)) S (pResidual_sup_sylow_eq_top S)
    ((ChapterB.isMinimalParabolicOver_top_iff S).mp hP').1
  have hlift := isCoatom_comap_of_surjective hq hmax
  change IsCoatom (((T : Subgroup G).map q).comap q) at hlift
  have hker : q.ker ≤ (T : Subgroup G) := by
    rw [QuotientGroup.ker_mk']
    exact hCT
  rwa [comap_map_eq_self hker] at hlift

end CFSG.Quasithin.ChapterE.ThompsonAction
