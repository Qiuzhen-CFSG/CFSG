module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.ComponentAutomizer
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.Nonsolvable
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
/-!
# The Sylow orbit of an actual perfect source factor

Let Y be a normal Sylow supplement and let a nontrivial perfect factor L
be normalized by Y. The Sylow orbit of L is normal in the whole group and
lies in its two-residual. It cannot lie in the solvable minimal-parabolic
core, so the original normal-subgroup dichotomy makes it the full residual.
This supplies the orbit condition needed by the literal component automizer.

Source: Aschbacher–Smith, B.6.8–B.6.9, printed pp.114–116.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]

/-- The original Sylow conjugates of the source factor generate the whole residual. -/
theorem source_factor_orbit_eq_residual
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (Y L : Subgroup G) [Y.Normal] [Group.IsPerfect L] [Nontrivial L]
    (hn : Y ≤ normalizer (L : Set G)) (hgen : Y ⊔ (T : Subgroup G) = ⊤) :
    componentOrbit L (T : Subgroup G) = pResidual 2 G := by
  have hLR : L ≤ pResidual 2 G := by
    let : Group.IsNilpotent (G ⧸ pResidual 2 G) := (isPGroup_quotient_pResidual 2).isNilpotent
    exact le_of_isPerfect_of_solvable_quotient _ _
  have hconj (t : T) : L.map (MulAut.conj (t : G)).toMonoidHom ≤ pResidual 2 G := by
    exact (map_mono hLR).trans_eq
      (normal_iff_map_conj_eq.mp (inferInstance : (pResidual 2 G).Normal) t)
  have hYn : Y ≤ normalizer (componentOrbit L (T : Subgroup G) : Set G) := by
    apply (le_iInf fun t : T => ?_).trans (iInf_normalizer_le_normalizer_iSup _)
    have hm := (map_mono (f := (MulAut.conj (t : G)).toMonoidHom) hn).trans
      (L.le_normalizer_map _)
    have he : Y.map (MulAut.conj (t : G)).toMonoidHom = Y :=
      normal_iff_map_conj_eq.mp (inferInstance : Y.Normal) t
    rwa [he] at hm
  let : (componentOrbit L (T : Subgroup G)).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    exact sup_le hYn (le_normalizer_componentOrbit L (T : Subgroup G))
  have hnot : ¬ componentOrbit L (T : Subgroup G) ≤ minimalParabolicCore T hP := by
    intro hh
    let := minimalParabolic_core_solvable T hP
    let f := inclusion ((le_componentOrbit L (T : Subgroup G)).trans hh)
    exact Group.IsPerfect.not_isSolvable L
      (Group.isSolvable_of_isSolvable_injective (f := f) (inclusion_injective _))
  exact le_antisymm (iSup_le hconj)
    ((minimalParabolic_normal_subgroup_residual_dichotomy T hP _).resolve_left hnot)

end CFSG.Quasithin.ChapterB
