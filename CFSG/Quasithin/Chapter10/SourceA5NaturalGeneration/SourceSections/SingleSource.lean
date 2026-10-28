module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.PairedSource
public import Theory.GroupTheory.CComponent.QuasisimpleResidualNormal
/-!
# Nonnormality excludes the single natural source

The reduced centralizer quotient has solvable kernel. In the single source
case its 2-residual is quasisimple, forcing the original C-component to be
normal, contrary to its prescribed Sylow orbit.
Source: Aschbacher–Smith E.2.3 and 10.2.3(4), pp.216–217 and746.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE.ThompsonAction ChapterB ChapterB.SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
theorem source_original_not_quasisimple_source
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    let X := localJoin T L
    let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
    let U := D.moduleSubgroup.subgroupOf X
    letI := (source_parabolic_module_reduced D).normal
    letI := (source_parabolic_module_reduced D).elementary
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    let α := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    ¬ elementaryAbelianMaxJ (S : Subgroup X) ≤ centralizer (U : Set X) →
      ¬ IsQuasisimple (generalizedFitting (offenderSubgroup α)) := by
  let X := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf X
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = C := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  dsimp only
  intro hJ hqs
  have hP := source_a5_minimal_parabolic D e hn
  have hcore : pCore 2 (X ⧸ C) = ⊥ := hU.quotient_pCore_eq_bot
  have hne : q.ker ≠ ⊤ := by
    intro he
    apply hJ
    change elementaryAbelianMaxJ (S : Subgroup X) ≤ C
    rw [←hk,he]
    exact le_top
  have hp := (minimalParabolic_reduced_image S hP q hq hcore hne).2
  have hff : IsFFModule α := by
    obtain hf | ⟨_,hf,_,_,_⟩ := lemma_B_2_7 U q hq hk S
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top S).trans hf.1)).elim
    · exact hf
  have hr := (source_quasisimple_fitting_eq_residual (S.mapSurjective hq) hp Y
    (offender_generation (S.mapSurjective hq) hp α hff hcore).2 hqs).2
  have hker : q.ker ≤ minimalParabolicCore S hP := by
    rw [hk]
    exact RankOneBaumann.reduced_centralizer_le_core S hP U hU hJ
  let : Group.IsSolvable (minimalParabolicCore S hP) := minimalParabolic_core_solvable S hP
  let : Group.IsSolvable q.ker := Group.isSolvable_of_isSolvable_injective (inclusion_injective hker)
  have hL : (L.subgroupOf X).IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  have hnormal := hL.normal_of_solvable_kernel_quasisimple_residual _ q hq hr
  exact hn (le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
    ((le_componentOrbit L T).trans le_sup_left)).mp hnormal))
end CFSG.Quasithin.Chapter10
