module
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.Nonsolvable
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.FrattiniSource
/-!
# Solvability detected on the original reduced action

For a reduced module moved by the Sylow Thompson subgroup, its centralizer
lies in the minimal-parabolic core. That core is solvable by B.6.8. A
solvable faithful action quotient therefore makes the original group
solvable, by the literal kernel extension.

Source: Aschbacher–Smith B.6.8(3),(6), printed pp.114–115.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB
universe u v
variable {G : Type u} [Group G] [Finite G]
theorem solvable_of_reduced_minimalParabolic_action {D : Type v} [Group D] [Finite D]
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* D) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) (hs : Group.IsSolvable D) :
    Group.IsSolvable G := by
  let : Group.IsSolvable (minimalParabolicCore T hP) := minimalParabolic_core_solvable T hP
  have hc : q.ker ≤ minimalParabolicCore T hP :=
    hker ▸ RankOneBaumann.reduced_centralizer_le_core T hP U hU hJ
  let : Group.IsSolvable q.ker := Group.isSolvable_of_isSolvable_injective (inclusion_injective hc)
  let : Group.IsSolvable D := hs
  let e := QuotientGroup.quotientKerEquivOfSurjective q hq
  let : Group.IsSolvable (G ⧸ q.ker) :=
    Group.isSolvable_of_isSolvable_injective e.injective
  exact (Group.isSolvable_iff_subgroup_quotient q.ker).mpr ⟨inferInstance,inferInstance⟩

end CFSG.Quasithin.ChapterB
