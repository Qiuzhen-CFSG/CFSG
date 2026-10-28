module

public import CFSG.Quasithin.Chapter3.Section02.Basic
public import Theory.GroupTheory.ReducedNormal.AmbientInclusion

/-!
# The ambient elementary module in the Fundamental Setup

A.1.11 places the original reduced module of L₀T inside R₂(M).
Normality of R₂(M) contains all M-conjugates of V, so their join V_M
is elementary abelian. These are the actual subgroups constructed in the
FSU, supplying the elementary section used to invoke D.3.2.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the opening of the proof of Lemma 3.2.2, printed p.579.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
universe u
variable {G : Type u} [Group G] [Finite G]
  {K : GroupClass.{u}} {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup K T L)

theorem join_reduced_le_maximal_reduced
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L) :
    (reducedTwoSubgroup (localJoin T L)).map (localJoin T L).subtype ≤
      (reducedTwoSubgroup D.maximalLocal).map D.maximalLocal.subtype := by
  obtain ⟨hm, hj, _⟩ := D.lemma_3_2_3_uniqueness h127
  exact reducedPSubgroup_ambient_le T _ _ le_sup_right hj
    (D.simpleQTKE.evenCharacteristic T _ hm (le_sup_right.trans hj))

theorem fullModule_le_reduced
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L) :
    D.fullModule ≤ (reducedTwoSubgroup D.maximalLocal).map D.maximalLocal.subtype := by
  apply iSup_conjugates_le_of_le_normalizer _ _ _
    (D.module_le_reduced.trans (D.join_reduced_le_maximal_reduced h127))
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
    (reducedTwoSubgroup D.maximalLocal).le_normalizer_map D.maximalLocal.subtype

theorem fullModule_elementary
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L) :
    IsElementaryAbelian 2 D.fullModule := by
  let := (isPReduced_reducedPSubgroup (p := 2) (G := D.maximalLocal)).elementary
  let : IsElementaryAbelian 2
      ((reducedTwoSubgroup D.maximalLocal).map D.maximalLocal.subtype) :=
    IsElementaryAbelian.map D.maximalLocal.subtype
  exact IsElementaryAbelian.of_le (D.fullModule_le_reduced h127)

end CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
