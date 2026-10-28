module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.ComponentSelection
public import Theory.GroupTheory.SolvableResidual.TwoSupplement
/-!
# The original symmetric-five residual is the required A₅ local component

Transport the faithful action to the actual centralizer quotient, so the
component-lifting theorem works in the original universe. The selected
component is normal and cannot lie in the solvable minimal-parabolic core;
it therefore supplements the Sylow subgroup and equals O²(G). Its
intrinsic two-core quotient is the concrete alternating group A₅.

Source: Aschbacher–Smith C.1.26, p.132.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The marked symmetric-five action makes the actual two-residual the
selected C-component and identifies its intrinsic two-core quotient. -/
theorem symmetric_five_residual_component
    {C : GroupClass.{u}} (h36 : A36Input C) (hG : IsSQTK C G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G)) :
    (pResidual 2 G).IsCComponent ∧
      Nonempty ((pResidual 2 G ⧸ pCore 2 (pResidual 2 G)) ≃* alternatingGroup (Fin 5)) := by
  let C0 := centralizer (U : Set G)
  let π := QuotientGroup.mk' C0
  let e : (G ⧸ C0) ≃* Equiv.Perm (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective C0
  have hkπ : π.ker = centralizer (U : Set G) := QuotientGroup.ker_mk' C0
  let A5 := alternatingGroup (Fin 5)
  let : IsQuasisimple A5 := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let A := A5.map e.symm.toMonoidHom
  let eA : A ≃* A5 := (A5.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm
  have hA : IsComponent (G ⧸ C0) A :=
    (show IsComponent (Equiv.Perm (Fin 5)) A5 from
      ⟨(inferInstance : A5.Normal).isSubnormal,inferInstance⟩).map_equiv e.symm
  have hs : ¬ Group.IsSolvable G := by
    intro hs
    let := hs
    let : Group.IsSolvable (Equiv.Perm (Fin 5)) := Group.isSolvable_of_surjective hq
    exact hA.isCComponent.not_isSolvable
      (Group.isSolvable_of_isSolvable_injective (f := eA.toMonoidHom) eA.injective)
  obtain ⟨L,hL,hm,⟨eL⟩,hc,hn⟩ := exists_five_component_of_reduced_module
    h36 hG T hP U hU hJ π hπ hkπ hs A hA eA
  let : A.Normal := Normal.map inferInstance e.symm.toMonoidHom e.symm.surjective
  let : L.Normal := normalizer_eq_top_iff.mp (top_unique (hn ⊤ (by
    rw [normalizer_eq_top]; exact le_top)))
  have hprod : L ⊔ (T : Subgroup G) = ⊤ := by
    obtain hb | hb := minimalParabolic_normal_subgroup_dichotomy T hP L
    · let : Group.IsSolvable (minimalParabolicCore T hP) := minimalParabolic_core_solvable T hP
      exact (hL.not_isSolvable (Group.isSolvable_of_isSolvable_injective (inclusion_injective hb))).elim
    · simpa only [sup_comm] using hb
  let : Group.IsPerfect L := hL.perfect
  have hr : pResidual 2 G = L := (residuals_of_perfect_normal_sup_twoGroup L
    (T : Subgroup G) T.isPGroup' hprod).1
  rw [hr]
  exact ⟨hL,⟨eL⟩⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
