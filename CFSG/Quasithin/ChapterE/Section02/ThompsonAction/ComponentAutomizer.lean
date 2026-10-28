module

public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.ComponentAutomizer.Source
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.Basic

/-!
# The component automizer in the original nonsolvable reduced action

The actual centralizer quotient of U is minimal parabolic. Its kernel is in
the solvable maximal-overgroup core, so nonsolvability survives. Apply the
proved B.6.8 source theorem to this very quotient. The resulting factor and
its automizer retain both successive quotient maps and the original Sylow
image. The module on an irreducible chief section and its extension to this
automizer remain a separate representation-theoretic step in B.6.9.

Source: Aschbacher–Smith, B.6.8–9 and E.2.3, printed pp.114–116 and216–217
(1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterE.ThompsonAction
variable {G : Type*} [Group G] [Finite G]

/-- A literal source component automizer, constructed on the original reduced centralizer quotient. -/
theorem source_nonsolvable_star_automizer
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U) (hs : ¬ Group.IsSolvable G)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    let := hU.normal
    let C := centralizer (U : Set G)
    let S := T.mapSurjective (QuotientGroup.mk'_surjective C)
    ∃ hp : ChapterB.IsMinimalParabolicOver S ⊤,
      ∃ L : Subgroup (ChapterB.minimalParabolicStarQuotient S hp),
        L ≤ pResidual 2 (ChapterB.minimalParabolicStarQuotient S hp) ∧
        IsSimpleGroup L ∧ ¬ IsMulCommutative L ∧
        IsComponent (ChapterB.minimalParabolicStarQuotient S hp) L ∧
        componentOrbit L (ChapterB.minimalParabolicStarSylow S hp) =
          pResidual 2 (ChapterB.minimalParabolicStarQuotient S hp) ∧
        ∃ R : Sylow 2 (NormalizerAction.Star L),
          (R : Subgroup (NormalizerAction.Star L)) =
            ((ChapterB.minimalParabolicStarSylow S hp : Subgroup _).subgroupOf
              (normalizer (L : Set (ChapterB.minimalParabolicStarQuotient S hp)))).map
                (NormalizerAction.quotient L) ∧
          ChapterB.IsMinimalParabolicOver R ⊤ := by
  let := hU.normal
  let C := centralizer (U : Set G)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hn : q.ker ≠ ⊤ := by
    intro he
    apply hJ
    rw [show centralizer (U : Set G) = q.ker from (QuotientGroup.ker_mk' C).symm, he]
    exact le_top
  obtain ⟨hk,hp⟩ := ChapterB.minimalParabolic_reduced_image T hP q hq
    hU.quotient_pCore_eq_bot hn
  have hsA : ¬ Group.IsSolvable (G ⧸ C) := by
    intro hA
    let := hA
    let := ChapterB.minimalParabolic_core_solvable T hP
    let : Group.IsSolvable q.ker :=
      Group.isSolvable_of_isSolvable_injective (f := inclusion hk) (inclusion_injective hk)
    exact hs (Group.isSolvable_of_ker_le_range q.ker.subtype q (by rw [range_subtype]))
  exact ⟨hp,ChapterB.minimalParabolic_nonsolvable_star_automizer _ hp hsA⟩

end CFSG.Quasithin.ChapterE.ThompsonAction
